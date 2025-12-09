import sage
from sage.categories.groups import Groups
from sage.groups.matrix_gps.linear import LinearMatrixGroup_generic
from sage.matrix.constructor import Matrix, matrix
from sage.rings.infinity import infinity
from sage.rings.number_field.number_field import QuadraticField
from sage.all import latex, Integer
from sage.misc.cachefunc import cached_method
from sage.arith.misc import divisors
from sage.modular.cusps_nf import list_of_representatives, NFCusps_ideal_reps_for_levelN
from sage.modular.modsym.p1list_nf import psi
from extended_hilbert_modgroup.cusp_nf_wrt_lattice_ideal import NFCusp_wrt_lattice_ideal
from extended_hilbert_modgroup.extended_hilbert_modular_group_element import ExtendedHilbertModularGroupElement
from extended_hilbert_modgroup.cusp_nf_wrt_lattice_ideal import totally_positive_unit_group_generators
import logging

from hilbert_modgroup.upper_half_plane import ComplexPlaneProductElement__class

logger = logging.getLogger(__name__)
logger.setLevel(int(10))


def is_ExtendedHilbertModularGroup(x) -> bool:
    """
    Return `True` if ``x`` is an instance of an ExtendedHilbertModularGroup

    INPUT:

    - ``x`` -- something to test if it is an Extended Hilbert modular group or not

    OUTPUT:

    - boolean

    EXAMPLES::

        sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
        sage: from extended_hilbert_modgroup.all import is_ExtendedHilbertModularGroup
        sage: is_ExtendedHilbertModularGroup(1)
        False
        sage: H = ExtendedHilbertModularGroup(5)
        sage: is_ExtendedHilbertModularGroup(H)
        True
        sage: K3.<a> = QuadraticField(3)
        sage: lattice_ideal = K3.fractional_ideal(5)
        sage: level_ideal = K3.fractional_ideal(7)
        sage: H = ExtendedHilbertModularGroup(K3, lattice_ideal, level_ideal)
        sage: is_ExtendedHilbertModularGroup(H)
        True
    """
    return isinstance(x, ExtendedHilbertModularGroup_class)


def ExtendedHilbertModularGroup(number_field, lattice_ideal = None, level_ideal = None, tp_units = True):
    r"""
    Create the Extended Hilbert modular group PGL_2^+(Fractional_ideal(1) \oplus lattice_ideal, level_ideal)
    (or PSL_2(Fractional_ideal(1) \oplus lattice_ideal, level_ideal)), of order 2, consisting of matrices of
    determinant in U_K^+ (or 1).

    INPUT:

    - ``number_field`` (NumberField)       -- a totally real field.
    - ``lattice_ideal`` (NumberFieldIdeal)  -- an ideal in totally real field.
    - ``level_ideal`` (NumberFieldIdeal)    -- an ideal in the same field.
    - ``tp_units `` (bool)  - ``True`` if you want the determinant in U_K^+ and ``False`` if 1.

    EXAMPLES::

        sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
        sage: number_field = 5
        sage: ExtendedHilbertModularGroup(number_field)
        Hilbert modular group PGL_2^+(Fractional ideal (1) + Fractional ideal (1), Fractional ideal (1)) of order
        2 over Number Field in a with defining polynomial x^2 - 5 with a = 2.236067977499790? consisting of
        matrices of determinant in U_K^+.
        sage: K1.<a> = QuadraticField(2)
        sage: lattice_ideal = K1.fractional_ideal(3)
        sage: ExtendedHilbertModularGroup(K1, lattice_ideal)
        Hilbert modular group PGL_2^+(Fractional ideal (1) + Fractional ideal (3), Fractional ideal (1)) of
        order 2 over Number Field in a with defining polynomial x^2 - 2 with a = 1.414213562373095? consisting
        of matrices of determinant in U_K^+.
        sage: level_ideal = K1.fractional_ideal(5)
        sage: ExtendedHilbertModularGroup(K1, lattice_ideal, level_ideal)
        Hilbert modular group PGL_2^+(Fractional ideal (1) + Fractional ideal (3), Fractional ideal (5)) of
        order 2 over Number Field in a with defining polynomial x^2 - 2 with a = 1.414213562373095? consisting
        of matrices of determinant in U_K^+.
        sage: ExtendedHilbertModularGroup(K1, lattice_ideal, level_ideal, tp_units = False)
        Extended Hilbert modular group PSL_2(Fractional ideal (1) +  lattice_ideal, level_ideal) of order 2 over
        Number Field in a with defining polynomial x^2 - 2 with a = 1.414213562373095? consisting of matrices
        of determinant 1.

    """
    if isinstance(number_field, (int, Integer)):
        if number_field > 0:
            number_field = QuadraticField(number_field)
        else:
            raise ValueError("The input must be a positive integers")
    if isinstance(number_field, sage.rings.number_field.number_field_base.NumberField):
        if not number_field.is_totally_real():
            raise ValueError("The input must be a totally real Number Field")
    if not lattice_ideal:
        lattice_ideal = number_field.fractional_ideal(1)
    if not level_ideal:
        level_ideal = number_field.fractional_ideal(1)
    degree = Integer(2)
    if not (
            lattice_ideal.number_field() == number_field or level_ideal.number_field() == number_field or lattice_ideal.is_coprime(
            level_ideal)):
        raise ValueError(
            "The lattice ideal and level ideal must be an ideal of the same number field and coprime to each other")
    if tp_units:
        name = f'Hilbert modular group PGL_2^+({number_field.fractional_ideal(1)} + {lattice_ideal}, {level_ideal}) of order 2 over {number_field} consisting of matrices of determinant in U_K^+.'
    else:
        name = f'Extended Hilbert modular group PSL_2({number_field.fractional_ideal(1)} +  lattice_ideal, level_ideal) of order 2 over {number_field} consisting of matrices of determinant 1.'
    ltx = 'PGL2^+[OK + lattice_ideal]'.format(degree, latex(number_field))
    return ExtendedHilbertModularGroup_class(number_field, lattice_ideal=lattice_ideal, level_ideal=level_ideal,
                                             tp_units = tp_units, sage_name=name, latex_string=ltx)


class ExtendedHilbertModularGroup_class(LinearMatrixGroup_generic):
    r"""
    Class for Extended Hilbert modular groups, here defined as either P[OK + I] (default) with determinants that are totally positive units in OK.
    """

    Element = ExtendedHilbertModularGroupElement

    def __init__(self, number_field, lattice_ideal, level_ideal, tp_units, sage_name, latex_string):
        r"""
         Init an Extended Hilbert modular group of the form PGL2^+[OK+lattice_ideal].

        INPUT:

        - ``lattice_ideal`` - NumberFieldFractionalIdeal
        - ``sage_name`` - string
        - ``latex_string`` - string

        EXAMPLES::
            sage: from extended_hilbert_modgroup.extended_hilbert_modular_group_class import ExtendedHilbertModularGroup_class
            sage: K = QuadraticField(5)
            sage: lattice_ideal = K.different()
            sage: level_ideal = K.fractional_ideal(3)
            sage: ltx = 'PGL2^+[OK + lattice_ideal]'.format(2, latex(number_field))
            sage: name = f"Extended Hilbert modular group PGL_2(OK + lattice_ideal, level_ideal) over {K}"
            sage: ExtendedHilbertModularGroup_class(number_field =  K, lattice_ideal = lattice_ideal, level_ideal = level_ideal, tp_units= True,
            ....: sage_name = name, latex_string = ltx)
            Extended Hilbert modular group PGL_2(OK + lattice_ideal, level_ideal) over Number Field in a with
            defining polynomial x^2 - 5 with a = 2.236067977499790?
            sage: H1 = ExtendedHilbertModularGroup(5)
            sage: TestSuite(H1).run()
            sage: H1(1)
            [1 0]
            [0 1]
            sage: H1([1, 1, 0, 1])
            [1 1]
            [0 1]
            sage: H1([1, H1.OK().gens()[0], 0, 1])
            [          1 1/2*a + 1/2]
            [          0           1]

        """
        self._number_field = number_field
        self._lattice_ideal = lattice_ideal
        self._level_ideal = level_ideal
        self._OK = number_field.ring_of_integers()
        self._tp_units = tp_units
        # Instance data related to cusps
        self._ncusps = None
        self._cusps = []
        self._ideal_cusp_representatives = []
        self._cusp_normalizing_maps = {}
        self._cusp_normalizing_maps_inverse = {}
        super(ExtendedHilbertModularGroup_class, self).__init__(degree = Integer(2), base_ring=number_field,
                                                                special = False,
                                                                sage_name = sage_name,
                                                                latex_string = latex_string,
                                                                category = Groups().Infinite(),
                                                                invariant_form=None)

    def number_field(self):
        """
        Return the number field associated to self.

        EXAMPLES::

            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: K = QuadraticField(5)
            sage: H = ExtendedHilbertModularGroup(K)
            sage: H.number_field()
            Number Field in a with defining polynomial x^2 - 5 with a = 2.236067977499790?
        """
        return self._number_field

    def lattice_ideal(self):
        """
        Return the lattice_ideal associated to self.

        EXAMPLES::

            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: H = ExtendedHilbertModularGroup(5)
            sage: H.lattice_ideal()
            Fractional ideal (1)
        """
        return self._lattice_ideal

    def level_ideal(self):
        """
        Return the level_ideal associated to self.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: K = QuadraticField(3)
            sage: H = ExtendedHilbertModularGroup(K)
            sage: H.level_ideal()
            Fractional ideal (1)
            sage: level_ideal = K.fractional_ideal(7)
            sage: H = ExtendedHilbertModularGroup(K, level_ideal = level_ideal)
            sage: H.level_ideal()
            Fractional ideal (7)

        """
        return self._level_ideal

    def tp_units(self):
        """
        Return the tp_units value associated to self.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: K = QuadraticField(3)
            sage: H = ExtendedHilbertModularGroup(K)
            sage: H.tp_units()
            True
            sage: tp_units = False
            sage: H = ExtendedHilbertModularGroup(K, tp_units = False)
            sage: H.tp_units()
            False
        """
        return self._tp_units

    def OK(self):
        """
        Return the ring of integers associated with self.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: H = ExtendedHilbertModularGroup(5)
            sage: H.OK()
        """
        return self._OK

    def generators(self):
        r"""
        Return a list of generators of ``self``.

        EXAMPLES::

            sage: from extended_hilbert_modgroup.all  import ExtendedHilbertModularGroup
            sage: K1.<a> = QuadraticField(2)
            sage: H = ExtendedHilbertModularGroup(K1)
            sage: H.generators()
            [
            [1 1]  [1 a]  [1 0]  [1 0]  [2*a + 3       0]
            [0 1], [0 1], [1 1], [a 1], [      0       1]
            ]
            sage: lattice_ideal = K1.fractional_ideal(3)
            sage: H = ExtendedHilbertModularGroup(K1, lattice_ideal)
            sage: H.generators()
            [
            [  1 1/3]  [    1 1/3*a]  [1 0]  [  1   0]  [2*a + 3       0]
            [  0   1], [    0     1], [3 1], [3*a   1], [      0       1]
            ]
            sage: lattice_ideal = K1.fractional_ideal(1)
            sage: level_ideal = K1.fractional_ideal(3)
            sage: H = ExtendedHilbertModularGroup(K1, lattice_ideal, level_ideal)
            sage: H.generators()
            [
            [-a + 1      0]  [-1  0]  [a + 1     0]  [ a -1]  [-a -1]
            [     3 -a - 1], [ 3 -1], [    3 a - 1], [ 3 -a], [ 3  a],

            [-a - 1      0]  [a - 1     0]  [1 1]  [1 a]  [1 0]  [  1   0]
            [     3 -a + 1], [    3 a + 1], [0 1], [0 1], [3 1], [3*a   1],

            [2*a + 3       0]
            [      0       1]
            ]
            sage: H = ExtendedHilbertModularGroup(K1, lattice_ideal, level_ideal, tp_units = False)
            sage: H.generators()
            [
            [-a + 1      0]  [-1  0]  [a + 1     0]  [ a -1]  [-a -1]
            [     3 -a - 1], [ 3 -1], [    3 a - 1], [ 3 -a], [ 3  a],

            [-a - 1      0]  [a - 1     0]  [1 1]  [1 a]  [1 0]  [  1   0]
            [     3 -a + 1], [    3 a + 1], [0 1], [0 1], [3 1], [3*a   1]
            ]

        """
        gens = []
        tp_units = self.tp_units()
        lattice_ideal = self.lattice_ideal()
        level_ideal = self.level_ideal()
        number_field = self.number_field()
        Lreps = list_of_representatives(level_ideal)
        for d in level_ideal.residues():
            if (d != 0 and d != 1 and number_field.fractional_ideal(d).is_coprime(level_ideal)):
                Lds = [P * lattice_ideal * level_ideal for P in Lreps if
                       (P * lattice_ideal * level_ideal).is_principal()]
                C = Lds[0]
                c = (C).gens_reduced()[0]
                A1 = c * (lattice_ideal.inverse())
                A2 = number_field.fractional_ideal(d)
                r = A1.element_1_mod(A2)
                b = -r / c
                a = (1 - r) / d
                gens.append(self.create_element(a, b, c, d))
        for x in self.lattice_ideal().inverse().basis():
            gens.append(self.T(x))
        for x in (self.lattice_ideal() * self.level_ideal()).basis():
            gens.append(self.L(x))
        if tp_units:
            tpunit_gen = totally_positive_unit_group_generators(number_field)
            for x in tpunit_gen:
                gens.append(self.E(x))
            return gens
        else:
            return gens

    @cached_method
    def S(self):
        """
        Return the element S = ( 0 & -1 // 1 & 0 ) of self.

        EXAMPLES::

            sage: from extended_hilbert_modgroup.all  import ExtendedHilbertModularGroup
            sage: K1.<a> = QuadraticField(2)
            sage: H = ExtendedHilbertModularGroup(K1)
            sage: H.S()
            [ 0 -1]
            [ 1  0]
        """
        return self([0, -1, 1, 0])

    @cached_method
    def T(self, a=1):
        """
        Return the element T^a = ( 1 & a // 0 & 1 ) of self.

        INPUT:

        - ``a`` -- integer in number field (default=1)

        EXAMPLES::

            sage: from extended_hilbert_modgroup.all  import ExtendedHilbertModularGroup
            sage: K2.<a> = QuadraticField(5)
            sage: H = ExtendedHilbertModularGroup(K2)
            sage: H.T()
            [1 1]
            [0 1]
            sage: u0, u1 = K2.unit_group().gens()
            sage: H.T(u0)
            [ 1 -1]
            [ 0  1]
            sage: H.T(u0*u1)
            [          1 1/2*a - 1/2]
            [          0           1]
        """
        return self([1, a, 0, 1])

    @cached_method
    def L(self, a):
        """
        Return the element L=( 1 & 0 // a & 1 ) of self.

        INPUT:

        - ``a`` -- integer in number field

        EXAMPLES::

            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: H = ExtendedHilbertModularGroup(5)
            sage: H.L(1)
            [1 0]
            [1 1]
            sage: u0,u1=H.base_ring().number_field().unit_group().gens()
            sage: H.L(u0)
            [ 1 0]
            [-1 1]
            sage: H.L(u0*u1)
            [          1           0]
            [1/2*a - 1/2           1]

        """
        return self([1, 0, a, 1])

    @cached_method
    def E(self, u):
        """
        Return the element U=( u & 0 // 0 & 1 ) of self.

        INPUT:
        - `u` is a totally positive unit in self.number_field().unit_group()

        EXAMPLES::

            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: H = ExtendedHilbertModularGroup(5)
            sage: H.E(1)
            [1 0]
            [0 1]
            sage: u0,u1=H.base_ring().number_field().unit_group().gens()
            sage: H.E(u0*u1)
            [-1/2*a + 3/2            0]
            [           0            1]


        """
        return self([u, 0, 0, 1])

    def create_element(self, a, b, c, d):
        r"""
        Return an element of Extended Hilbert Modular Group.

        INPUT:

        - a, b, c, d -- matrix entries.


        EXAMPLES::

            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: H = ExtendedHilbertModularGroup(5)
            sage: A = H.create_element(1, 1, 0, 1)
            sage: A in H
            True
        """
        return self([a, b, c, d])


    def random_element(self, *args, **kwds):
        r"""
        Return a 'random' element of this Extended Hilbert Modular Group.

        INPUT:

        - `args`, `kwds` -- arguments passed to the base ring's random element function
                            and are in turn passed to the random integer function.
                            See the documentation for "ZZ.random_element()" for details.


        EXAMPLES::

            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: H = ExtendedHilbertModularGroup(5)
            sage: A = H.random_element()
            sage: A in H
            True

        """
        a = self.number_field().random_element(**kwds)
        b = self.number_field().random_element(**kwds)
        return self.T(a) * self.L(b)

    @cached_method
    def cusps(self):
        """
        Return the inequivalent cusps of self.

        sage: from extended_hilbert_modgroup.all  import ExtendedHilbertModularGroup
        sage: K2.<a> = QuadraticField(5)
        sage: lattice_ideal = K2.fractional_ideal(1)
        sage: level_ideal = K2.fractional_ideal(3)
        sage: H = ExtendedHilbertModularGroup(K2, lattice_ideal, level_ideal)
        sage: H.cusps()
        [Cusp [0: 1] of Number Field in a with defining polynomial x^2 - 5 with a = 2.236067977499790? with respect to  lattice_ideal,
         Cusp [1: 3] of Number Field in a with defining polynomial x^2 - 5 with a = 2.236067977499790? with respect to  lattice_ideal]
        sage: lattice_ideal = K2.fractional_ideal(7)
        sage: H = ExtendedHilbertModularGroup(K2, lattice_ideal, level_ideal)
        sage: H.cusps()
        [Cusp [0: 7] of Number Field in a with defining polynomial x^2 - 5 with a = 2.236067977499790? with respect to  lattice_ideal,
         Cusp [1: 21] of Number Field in a with defining polynomial x^2 - 5 with a = 2.236067977499790? with respect to  lattice_ideal]
        """
        K = self.number_field()
        lattice_ideal = self.lattice_ideal()
        N = self.level_ideal()
        L = NFCusps_ideal_reps_for_levelN(N, nlists=3)
        # Return a list of lists (``nlists`` different lists) of prime ideals,coprime to ``N``, representing every ideal class of the number field.
        Laux = L[1] + L[2]
        Lreps = list_of_representatives(lattice_ideal * N)
        Lcusps = []
        for A in L[0]:
            # find B in inverse class:
            if A.is_trivial():
                B = K.ideal(1)  # B = k.unit_ideal() produces an error because we need fract ideal
                g = 1
            else:
                Lbs = [P for P in Laux if (P * A).is_principal()]
                B = Lbs[0]
                g = (A * B).gens_reduced()[0]
            for d in divisors(N):  # for every divisor of N we have to find cusps
                # find deltaprime coprime to B in inverse class of d*A*lattice_ideal
                # by searching in our list of auxiliary prime ideals
                Lds = [P for P in Laux if (P * lattice_ideal * d * A).is_principal() and P.is_coprime(B)]
                deltap = Lds[0]
                a = (deltap * lattice_ideal * d * A).gens_reduced()[0]
                I = d + N / d
                # special case: A=B=d=<1>:
                if a.is_one() and I.is_trivial():
                    Lcusps.append(NFCusp_wrt_lattice_ideal(lattice_ideal, 0, 1, lreps=Lreps))
                else:
                    if self.tp_units():
                        gens = totally_positive_unit_group_generators(K)
                    else:
                        u = K.unit_group().gens_values()
                        gens = [t**2 for t in u]
                    for b in I.invertible_residues_mod(gens):
                        M = d.prime_to_idealM_part(I)
                        deltAM = deltap * lattice_ideal * A * M
                        u = (B * deltAM).element_1_mod(I)
                        v = (I * B).element_1_mod(deltAM)
                        newb = u * b + v
                        # build AB-matrix
                        # ----> extended gcd for k.ideal(a), k.ideal(newb)
                        A1 = a * (lattice_ideal.inverse()) * (A.inverse())
                        A2 = newb * B.inverse()
                        r = A2.element_1_mod(A1)
                        a1 = (r / newb) * g
                        b1 = -(1 - r) / a * g
                        # if xa + yb = 1, cusp = y*g /a
                        ABM = [a1, b1, a, newb]
                        Lcusps.append(NFCusp_wrt_lattice_ideal(lattice_ideal, a1, a, lreps=Lreps))
        self._cusps = Lcusps
        return self._cusps

    def ncusps(self):
        """
        Return the number of cusp associated to self.

            sage: from extended_hilbert_modgroup.all  import ExtendedHilbertModularGroup
            sage: K2.<a> = QuadraticField(5)
            sage: H = ExtendedHilbertModularGroup(K2)
            sage: H.ncusps()
            1
            sage: level_ideal = K6.fractional_ideal(3)
            sage: H = ExtendedHilbertModularGroup(K2, level_ideal = level_ideal)
            sage: H.ncusps()
            4
            sage: K2.<a> = QuadraticField(5)
            sage: lattice_ideal = K2.fractional_ideal(1)
            sage: level_ideal = K2.fractional_ideal(3)
            sage: H = ExtendedHilbertModularGroup(K2, level_ideal = level_ideal)
            sage: H.ncusps()
        """
        K = self.number_field()
        N = self.level_ideal()
        if self.tp_units():
            gens = totally_positive_unit_group_generators(K)
        else:
            u = K.unit_group().gens_values()
            gens = [K(t ** 2) for t in u]
        s = sum([len((d + N / d).invertible_residues_mod(gens)) for d in divisors(N)])
        self._ncusps = s * K.class_number()
        return self._ncusps

    @cached_method
    def coset_matrices(self):
        """
        Return the list of right cosets representatives of GL_2^+(OK oplus ida, idn) in GL_2(OK oplus ida).

            sage: from extended_hilbert_modgroup.all  import ExtendedHilbertModularGroup
            sage: K2.<a> = QuadraticField(5)
            sage: lattice_ideal = K2.fractional_ideal(1)
            sage: level_ideal = K2.fractional_ideal(3)
            sage: H = ExtendedHilbertModularGroup(K2, lattice_ideal, level_ideal)
            sage: H.coset_matrices()
            [
            [           0           -1]  [-1/2*a + 1/2            0]
            [           1 -3/2*a - 1/2], [           1 -1/2*a - 1/2],

            [1/2*a + 1/2           0]  [ 0 -1]  [ 1 -1]  [ 0 -1]
            [          1 1/2*a - 1/2], [ 1 -a], [ 1  0], [ 1  a],

            [-1/2*a - 1/2            0]  [1/2*a - 1/2           0]
            [           1 -1/2*a + 1/2], [          1 1/2*a + 1/2],

            [          0          -1]  [1 0]
            [          1 3/2*a + 1/2], [3 1]
            ]
            sage: from sage.modular.modsym.p1list_nf import psi
            sage: psi(level_ideal)
            10
            sage: len(H.coset_matrices())
            10
            sage: level_ideal = K2.fractional_ideal(7)
            sage: H = ExtendedHilbertModularGroup(K2, lattice_ideal, level_ideal)
            sage: len(H.coset_matrices()) == psi(level_ideal)
            True
        """
        N = self.level_ideal()
        K = self.number_field()
        lattice_ideal = self.lattice_ideal()
        H = ExtendedHilbertModularGroup(K, lattice_ideal)
        # L = [MSymbol(N, k(0), k(1), check=False)]
        # N.residues() = iterator through the residues mod N
        # L = L + [MSymbol(N, k(1), r, check=False) for r in N.residues()]
        L = []
        for D in divisors(N):
            if (D * lattice_ideal).is_principal():
                Dp = K.fractional_ideal(1)
                c = (D * lattice_ideal * Dp).gens_reduced()[0]
            else:
                it = K.primes_of_degree_one_iter()
                Dp = next(it)
                while not Dp.is_coprime(N) or not (Dp * D * lattice_ideal).is_principal():
                    Dp = next(it)
                c = (D * lattice_ideal * Dp).gens_reduced()[0]
            I = D + N / D
            for r in (N / D).residues():
                if I.is_coprime(r):
                    M = D.prime_to_idealM_part(N / D)
                    u = (Dp * M).element_1_mod(N / D)
                    d = u * r + (1 - u)  # Our M-symbol is (c: d) # print(r, u, c, d)
                    if d.is_zero():
                        L.append(H.create_element(1, -1 / c, c, d))
                    else:
                        B = K.fractional_ideal(c * lattice_ideal.inverse()).element_1_mod(K.fractional_ideal(d))
                        b = -B / c
                        a = (1 - B) / d
                        L.append(H.create_element(a, b, c, d))
        if not len(L) == psi(N):
            raise ValueError("Condition is not satisfying. Check again")
        return L

    def ideal_cusp_representatives(self):
        r"""
        Return a list of ideals corresponding to cusp representatives, i.e.
        ideal representatives of ideal classes.

        Note: We choose an ideal of smallest norm in each class.
            If the ideal given by sage is already minimal we return this.

        EXAMPLES::

            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: K2.<a> = QuadraticField(5)
            sage: lattice_ideal = K2.different()
            sage: level_ideal = K2.fractional_ideal(7)
            sage: H = ExtendedHilbertModularGroup(K2, lattice_ideal, level_ideal)
            sage: H.ideal_cusp_representatives()
            [Fractional ideal (1)]
            sage: K6.<a> = QuadraticField(10)
            sage: lattice_ideal = K6.different()
            sage: level_ideal = K6.fractional_ideal(7)
            sage: H = ExtendedHilbertModularGroup(K6, lattice_ideal, level_ideal)
            sage: H.ideal_cusp_representatives()
            [Fractional ideal (1), Fractional ideal (2, a)]


        """
        if not self._ideal_cusp_representatives:
            self._ideal_cusp_representatives = []

            def _find_equivalent_ideal_of_minimal_norm(c):
                for a in self.number_field().ideals_of_bdd_norm(c.norm() - 1).items():
                    for ideala in a[1]:
                        if (ideala * c ** -1).is_principal():
                            if c.norm() <= ideala.norm():
                                return c
                            return ideala
                return c

            for ideal_class in self.OK().class_group():
                c = ideal_class.ideal().reduce_equiv()
                # NOTE: Even though we use 'reduce_equiv' we are not guaranteed a representative
                #       with minimal **norm**
                #       To make certain we choose a representative of minimal norm explicitly.
                c = _find_equivalent_ideal_of_minimal_norm(c)
                self._ideal_cusp_representatives.append(c)
            # We finally sort all representatives according to norm.
            self._ideal_cusp_representatives.sort(key=lambda x: x.norm())
        return self._ideal_cusp_representatives

    def cusp_representative(self, cusp, return_map = False):
        r"""
        Return a representative cusp and optionally a corresponding map.

        INPUT:
        - ``cusp`` -- cusp
        - ``return_map`` -- bool (default: False)
            Set to True to also return the map giving the equivalence.

        EXAMPLES::

            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: K6.<a> = QuadraticField(10)
            sage: lattice_ideal = K6.different()
            sage: level_ideal = K6.fractional_ideal(7)
            sage: H = ExtendedHilbertModularGroup(K6, lattice_ideal, level_ideal)
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_lattice_ideal
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, 0, 1)
            sage: H.cusp_representative(c)
            Cusp [0: -2*a] of Number Field in a with defining polynomial x^2 - 10 with a = 3.162277660168380? with respect to  lattice_ideal
            sage: a = H.number_field().gen()
            sage: a = H.number_field().gen()
            sage: x, y = 3*a - 10, a-4
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, x, y)
            sage: H.cusp_representative(c)
            Cusp [2*a + 1: 14*a - 80] of Number Field in a with defining polynomial x^2 - 10 with a = 3.162277660168380? with respect to  lattice_ideal
            sage: K2.<a> = QuadraticField(5)
            sage: lattice_ideal = K2.fractional_ideal(2)
            sage: level_ideal = K2.fractional_ideal(3)
            sage: H = ExtendedHilbertModularGroup(K2, lattice_ideal, level_ideal, False)
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, 2, a)
            sage: H.cusp_representative(c)
            Cusp [0: 2] of Number Field in a with defining polynomial x^2 - 5 with a = 2.236067977499790? with respect to  lattice_ideal

        """
        for c in self.cusps():
            if return_map:
                t, B = cusp.is_Gamma0_wrt_lattice_ideal_equivalent(c, self.level_ideal(), Transformation = True)
                if t:
                    return c, self(B)
            else:
                t = cusp.is_Gamma0_wrt_lattice_ideal_equivalent(c, self.level_ideal())
                if t:
                    return c
        raise ArithmeticError(f"Could not find cusp representative for {cusp}")

    def cusp_normalizing_map(self, cusp, inverse=False, check=False):
        r"""
        Given a cusp (a:c) Return a matrix A = [[ a ,b ], [c , d]] in SL(2,K) such that
        A(Infinity)=(a:c).

        INPUT:
        - ``cusp`` -- Instance of NFCusp
        - ``inverse`` -- bool (default: False) set to True to return the inverse map
        - ``check`` -- bool (default: False) set to True to check the result

        If inverse = True then return A^-1

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: K3.<a> = QuadraticField(3)
            sage: lattice_ideal = K3.different()
            sage: level_ideal = K3.fractional_ideal(1)
            sage: H = ExtendedHilbertModularGroup(K3, lattice_ideal, level_ideal)
            sage: H.cusp_normalizing_map(H.cusps()[0])
            [    0 1/6*a]
            [ -2*a     0]
            sage: K2.<a> = QuadraticField(5)
            sage: lattice_ideal = K2.fractional_ideal(1)
            sage: level_ideal = K2.fractional_ideal(3)
            sage: H = ExtendedHilbertModularGroup(K2, lattice_ideal, level_ideal)
            sage: H.ncusps()
            2
            sage: H.cusps()[1]
            Cusp [1: 3] of Number Field in a with defining polynomial x^2 - 5 with a = 2.236067977499790? with respect to  lattice_ideal
            sage: H.cusp_normalizing_map(H.cusps()[1])
            [1 0]
            [3 1]
        """
        base_nf = self.number_field()
        if not isinstance(cusp, NFCusp_wrt_lattice_ideal) or cusp.number_field() != base_nf:
            raise ValueError(f"Input should be a NF cusp defined over {base_nf}!")
        ca, cb = (cusp.numerator(), cusp.denominator())
        if not (ca, cb) in self._cusp_normalizing_maps:
            # First find the equivalent representative
            # crep, B = self.cusp_representative(cusp,return_map=True)
            # crepa,crepb = crep.numerator(),crep.denominator()
            # crep_normalizing_map = self._cusp_normalizing_maps.get((crepa,crepb))
            # if not crep_normalizing_map:
            # Find a normalizing map of the cusp representative
            a, b, c, d = cusp.GHmatrix_wrt_lattice_ideal()
            det = a * d - b * c
            A = Matrix(self.number_field(), 2, 2, [a, b / det, c, d / det])
            # A = B.matrix().inverse()*crep_normalizing_map
            if check:
                infinity = NFCusp_wrt_lattice_ideal(self.lattice_ideal(), 1, 0)
                if infinity.apply(A.list()) != cusp or A.det() != 1:
                    msg = f"Did not get correct normalizing map A={A} to cusp: {cusp}"
                    raise ArithmeticError(msg)
            logger.debug(f"A={0}".format(A))
            logger.debug("A.det()={0}".format(A.det().complex_embeddings()))
            self._cusp_normalizing_maps_inverse[(ca, cb)] = A.inverse()
            self._cusp_normalizing_maps[(ca, cb)] = A
        if inverse:
            return self._cusp_normalizing_maps_inverse[(ca, cb)]
        else:
            return self._cusp_normalizing_maps[(ca, cb)]

    def apply_cusp_normalizing_map(self, cusp, z, inverse=False):
        """
        Apply the cusp normalizing map associated with the cusp to an element z
        INPUT:
        - `cusp` - an instance of NFcusp_wrt_lattice_ideal
        - `z` - an element in
             - the base number field
             - the set for cusps wrt lattice_ideal
             - in ComplexPlaneProductElement__class
        - `inverse` - set to True if applying the inverse map

        EXAMPLES::

            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup, NFCusp_wrt_lattice_ideal
            sage: K6.<a> = QuadraticField(10)
            sage: lattice_ideal = K6.fractional_ideal(1)
            sage: level_ideal = K6.fractional_ideal(1)
            sage: H = ExtendedHilbertModularGroup(K6, lattice_ideal, level_ideal)
            sage: H.apply_cusp_normalizing_map(H.cusps()[1], 1.0)
            -1.30152725142729
            sage: z = NFCusp_wrt_lattice_ideal(lattice_ideal, 1)
            sage: H.apply_cusp_normalizing_map(H.cusps()[1], z)
            Cusp [-535*a - 2585: 3286] of Number Field in a with defining polynomial x^2 - 10 with a = 3.162277660168380? with respect to  lattice_ideal
            sage: z = ComplexPlaneProductElement([CC(1,0),CC(1,0)]); z
            [1.00000000000000, 1.00000000000000]
            sage: H.apply_cusp_normalizing_map(H.cusps()[1], z)
            [-0.271814197142397, -1.30152725142729]
            sage: H.apply_cusp_normalizing_map(H.cusps()[1], 1).complex_embeddings()
            [-0.271814197142397, -1.30152725142729]
        """
        a, b, c, d = self.cusp_normalizing_map(cusp, inverse=inverse).list()
        if z == infinity:
            return a / c
        number_field = self.number_field()
        if isinstance(z, NFCusp_wrt_lattice_ideal) and z.number_field() == number_field:
            return z.apply([a, b, c, d])
        if z in number_field:
            return (a * z + b) / (c * z + d)
        if isinstance(z, ComplexPlaneProductElement__class) and \
                z.degree() == number_field.absolute_degree():
            return z.apply(matrix(2, 2, [a, b, c, d]))
        raise ValueError("Unsupported type for action with cusp normalizer! (z={0})".format(z))