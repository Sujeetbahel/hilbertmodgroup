%%cython
#cython: profile=True
"""
Cython versions of Extended Pullback algorithms.

Note: These are the algorithms that needs optimizing to make it all faster.
"""
from sage.all import ceil,floor,cartesian_product
from sage.arith.misc import gcd
from sage.structure.sage_object cimport SageObject
from hilbert_modgroup.upper_half_plane cimport UpperHalfPlaneProductElement__class
from sage.rings.number_field.number_field_element_base cimport NumberFieldElement_base

cpdef integral_coordinates_in_box(bounds):
    if not isinstance(bounds, list):
        raise ValueError
    n = len(bounds)
    coordinates = []
    for i in range(n):
        lower = ceil(bounds[i][0])
        upper = floor(bounds[i][1])
        if lower > upper:
            raise ValueError("Bounds must give interval of positive length.")
        coordinates.append(range(lower, upper + 1))
    # result = [tuple(x) for x in cartesian_product(coordinates)]
    # return result
    return list(cartesian_product(coordinates))

cpdef lattice_elements_in_box(lattice_basis, lattice_bounds, coordinate_bounds, norm_bound=None):
    coordinates = integral_coordinates_in_box(coordinate_bounds)
    result = []
    n = len(lattice_basis[0])
    for coordinate_vector in coordinates:
        is_within_bounds = True
        if norm_bound:
            norm = 1
        for i in range(n):
            alpha_i = 0
            for j in range(n):
                alpha_i = alpha_i + lattice_basis[i][j] * coordinate_vector[j]
            if alpha_i < lattice_bounds[i][0] or alpha_i > lattice_bounds[i][1]:
                # We need to discard this
                is_within_bounds = False
                break
            if norm_bound:
                norm = norm*alpha_i
        if norm_bound and abs(norm) > norm_bound:
            is_within_bounds = False
        # If we are within the bounds we add the number field element.
        if is_within_bounds:
            result.append(coordinate_vector)
    return result

cpdef coordinates_to_ideal_elements(coordinates,ideal_basis):
    result = []
    n = len(ideal_basis)
    for coordinate_vector in coordinates:
        if len(coordinate_vector) != n:
            raise ValueError("Coordinate need to have same length as basis!")
        element = 0
        for i,b in enumerate(ideal_basis):
            element += b * coordinate_vector[i]
        result.append(element)
    return result


cpdef find_candidate_cusps(p, z, use_lll=True, use_norm_bound=True, return_sigma_candidates=False,
                           initial_bd_d=None,
                           use_initial_bd_d=True):
    ideal_basis = p._construct_ideal(1).integral_basis()
    lattice_basis = p.basis_matrix_ideal()
    n = len(lattice_basis[0])
    # Make lattice basis to a nested list to avoid creation of FreeModule elements
    lattice_basis = [[lattice_basis[i][j] for j in range(n)] for i in range(n)]
    ## Initial bound:
    if use_lll:
        candidate_cusp = p.get_heuristic_closest_cusp(z)
    else:
        candidate_cusp = None
    if candidate_cusp and use_initial_bd_d:
        dist = distance_to_cusp_eg(p, candidate_cusp[0], candidate_cusp[1], z)
    else:
        dist = None
    if use_norm_bound:
        norm_bound_sigma = p._bound_for_sigma_norm(z, dist)
        norm_bound_sigma = norm_bound_sigma*(1+2**(-z[0].prec()/2)) # correct for numerical errors
    else:
        norm_bound_sigma = None
    if use_initial_bd_d and initial_bd_d and (not dist or dist > initial_bd_d):
        dist = initial_bd_d
        # norm_bound_rho = p._bound_for_rho_norm(z, dist)
    one = p.number_field()(1)
    coordinate_bounds = p._bound_for_sigma_coordinates(z, initial_bd_d=dist,use_initial_bd_d=use_initial_bd_d)
    embedding_bounds = p._bound_for_sigma_embeddings(z, initial_bd_d=dist,use_initial_bd_d=use_initial_bd_d)
    coordinate_bounds = [(-b,b) for b in coordinate_bounds]
    embedding_bounds = [(-b,b) for b in embedding_bounds]
    sigma_candidates_coordinates = lattice_elements_in_box(lattice_basis,
                                               embedding_bounds,
                                               coordinate_bounds, norm_bound=norm_bound_sigma)
    sigma_candidates = coordinates_to_ideal_elements(sigma_candidates_coordinates,
                                                             ideal_basis)
    if return_sigma_candidates:
        return sigma_candidates
    # To remove duplicates we keep track of the quotients rho/sigma (for sigma !=0)
    quotients = {}
    if not candidate_cusp or candidate_cusp[1] == 0:
        result = [(p.number_field()(1), p.number_field()(0))]
    elif candidate_cusp[0] == 0:
        result = [(p.number_field()(0), p.number_field()(1))]
    else:
        # We always have infinity since sigma=0 is always within the bounds.
        result = [candidate_cusp,(p.number_field()(1), p.number_field()(0))]
        q = candidate_cusp[0]/candidate_cusp[1]
        ngcd = gcd(candidate_cusp[0].norm(),candidate_cusp[1].norm())
        quotients = {q: (ngcd,(candidate_cusp[0],candidate_cusp[1]))}
    for s in sigma_candidates:
        if s == 0:
            continue
        rho_coordinate_bounds = p._bound_for_rho_coordinates(z, s, initial_bd_d=dist, use_initial_bd_d=use_initial_bd_d)
        rho_coordinate_bounds = [(-b,b) for b in rho_coordinate_bounds]
        rho_embedding_bounds = p._bound_for_rho_embeddings(z, s, initial_bd_d=dist, use_initial_bd_d=use_initial_bd_d)

        rho_candidates_coordinates = lattice_elements_in_box(lattice_basis, rho_embedding_bounds, rho_coordinate_bounds)
        rho_candidates = coordinates_to_ideal_elements(rho_candidates_coordinates, ideal_basis)

        for r in rho_candidates:
            if r == 0 and (r,one) not in result:
                result.append((r,one))
            if r == 0:
                continue
            quo = r/s
            ngcd = gcd(r.norm(), s.norm())
            if quo in quotients:
                # We try to pick the representative cusp that has the smallest norm gcd
                if ngcd < quotients[quo][0]:
                    result.remove(quotients[quo][1])
                else:
                    continue
            result.append((r,s))
            quotients[quo] = (ngcd,(r,s))
    return result

cpdef find_closest_cusp(p, z, return_multiple=False, use_lll=True, use_norm_bound=True):
    cusp_candidates = find_candidate_cusps(p, z, use_lll=use_lll, use_norm_bound=use_norm_bound)
    min_cusp = cusp_candidates[0]
    min_d = distance_to_cusp_eg(p,min_cusp[0], min_cusp[1], z)
    if return_multiple:
        min_cusp = [min_cusp]
    min_cusp_bound = p._bound_for_closest_cusp()
    eps = 2.0**(4-53) # Numerical precision for when we consider cusps to be equally close.
    # There may be many identical cusps in this list.
    # In particular there might be many
    for c in cusp_candidates[1:]:
        d = distance_to_cusp_eg(p, c[0],c[1], z)
        if abs(d-min_d)<eps and return_multiple:
            min_cusp.append(c)
        if d < min_d - 2*eps:
            if return_multiple:
                min_cusp = [c]
            else:
                min_cusp = c
            min_d = d
        if d < min_cusp_bound:
            break
    # We have already filtered away identical cusps but as a final stage
    # we also check if the minimal cusps are equal to any of the fixed representatives.
    # other than infinity which is already taken care of
    if p.group().ncusps() == 1:
        return min_cusp
    result = []
    for cusp in p.group().cusps()[1:]:
        c, d = cusp.numerator(),cusp.denominator()
        quo = c/d
        if return_multiple:
            for r,s in min_cusp:
                if s == 0:
                    result.append((r, s))
                elif r == 0 and (0,1) not in result:
                    result.append((0,1))
                elif r == 0:
                    continue
                elif r/s == quo and (c,d) not in result:
                    result.append((c,d))
                elif r/s != quo:
                    result.append((r,s))
        elif min_cusp[1] != 0 and min_cusp[0]/min_cusp[1] == quo:
            result = (c,d)
        else:
            result = min_cusp
    return result

cpdef distance_to_cusp_eg(SageObject p, NumberFieldElement_base r, NumberFieldElement_base s,
                        UpperHalfPlaneProductElement__class z):
    cdef list rlist,slist
    ideal_rs = p.group().ideal((r,s))
    #ideal_rs = r.parent().fractional_ideal(r,s)
    #print('ideal_rs=', ideal_rs)
    rlist = r.complex_embeddings()
    slist = s.complex_embeddings()
    n = len(slist)
    d = 1
    for i in range(n):
        d = d* ((-z._x[i] * slist[i] + rlist[i]) ** 2 * z._y[i] ** -1 + slist[i] ** 2 * z._y[i])
    d = ideal_rs.norm()**-1*d.sqrt()
    #print('d=', d)
    return d