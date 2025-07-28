import sage
from sage.categories.groups import Groups
from sage.groups.matrix_gps.linear import LinearMatrixGroup_generic
from sage.rings.infinity import infinity
from sage.rings.number_field.number_field import QuadraticField
from sage.all import latex, Integer, Matrix, matrix
from sage.misc.cachefunc import cached_method
#from sage.rings.number_field.order import is_NumberFieldOrder
# from hilbert_maass.modform.utils import Integer_t
#from sage.modular.cusps_nf import list_of_representatives
# from .upper_half_plane import ComplexPlaneOtimesK
from hilbert_modgroup.upper_half_plane import ComplexPlaneProductElement__class
from extended_hilbert_modgroup.cusp_nf_wrt_base_ideal import NFCusp_wrt_base_ideal
from extended_hilbert_modgroup.extended_hilbert_modular_group_element import ExtendedHilbertModularGroupElement
from extended_hilbert_modgroup.cusp_nf_wrt_base_ideal import gens_reduced_wrt_base_ideal, ideal_wrt_base_ideal
import logging

from sage.rings.number_field.unit_group import UnitGroup

logger = logging.getLogger(__name__)
logger.setLevel(int(10))


def is_ExtendedHilbertModularGroup(x) -> bool:
    """
    Return `True` if ``x`` is an instance of a ExtendedHilbertModularGroup

    INPUT:

    - ``x`` -- something to test if it is a Extended Hilbert modular group or not

    OUTPUT:

    - boolean

    EXAMPLES::

        sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup,is_ExtendedHilbertModularGroup
        sage: is_ExtendedHilbertModularGroup(1)
        False
        sage: H = ExtendedHilbertModularGroup(5)
        sage: is_ExtendedHilbertModularGroup(H)
        True
        sage: K = QuadraticField(3)
        sage: base_ideal = K.OK().fractional_ideal(2)
        sage: H = ExtendedHilbertModularGroup(base_ideal)
        sage: is_ExtendedHilbertModularGroup(H)
        True
    """
    return isinstance(x, ExtendedHilbertModularGroup_class)


def ExtendedHilbertModularGroup(base_ideal, projective=True):
    r"""
    Create the Extended Hilbert modular group P[OK+I], of order 2, consisting of matrices with determinants that are totally positive units in OK,
    where OK is the ring of integers and I is the base_ideal.


    INPUT:

    - ``base_ideal`` (NumberField)  -- a positive integer or totally real field or an ideal of totally real field.
    - ``projective`` (bool) - ``True`` if you want PSL(2,K) and ``False`` for SL(2,K)


    EXAMPLES::

        sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
        sage: ExtendedHilbertModularGroup(5)
        Extended Hilbert modular group of order 2 ( over Number Field in a with defining polynomial x^2 - 5 with a = 2.236067977499790?) of the form
        P[OK+OK], consisting of matrices with determinants that are totally positive units in OK, where OK is the ring of integers
        sage: ExtendedHilbertModularGroup(QuadraticField(5))
        Extended Hilbert modular group of order 2 ( over Number Field in a with defining polynomial x^2 - 5 with a = 2.236067977499790?) of the form
        P[OK+OK], consisting of matrices with determinants that are totally positive units in OK, where OK is the ring of integers
        sage: base_ideal = QuadraticField(5).different()
        sage: ExtendedHilbertModularGroup(base_ideal)
        Extended Hilbert modular group of order 2 (over Number Field in a with defining polynomial x^2 - 5 with a = 2.236067977499790?) of the forms
        P[OK+I], consisting of matrices with determinants that are totally positive units in OK, where OK is the ring of integers
        and I is Fractional ideal (-a)
    """
    if isinstance(base_ideal, (int, Integer)):
        if base_ideal > 0:
            number_field = QuadraticField(base_ideal)
            base_ideal = number_field.OK().fractional_ideal(1)
        else:
            raise ValueError("The input must be a positive integers")
    elif isinstance(base_ideal, sage.rings.number_field.number_field_base.NumberField):
        if base_ideal.is_totally_real():
            base_ideal = base_ideal.OK().fractional_ideal(1)
        else:
            raise ValueError("The input must be a totally real Number Field")
    elif isinstance(base_ideal, sage.rings.number_field.number_field_ideal.NumberFieldFractionalIdeal):
        if base_ideal.number_field().is_totally_real():
            base_ideal = base_ideal
        else:
            raise ValueError("The input must be an ideal of totally real field")
    else:
        raise ValueError(
            "The input must be a positive integer or totally real Number Field or an ideal of totally real field")
    if not projective:
        raise NotImplementedError(
            "Only Projective Extended Hilbert Modular Group P[OK + I] is implemented at the moment.")
    number_field = base_ideal.number_field()
    degree = Integer(2)
    if base_ideal == number_field.ring_of_integers().fractional_ideal(1):
        name = f'Extended Hilbert modular group of order 2 ( over {number_field}) of the form P[OK+OK], consisting of matrices with determinants that are totally positive units in OK, where OK is the ring of integers'
    else:
        name = f'Extended Hilbert modular group of order 2 (over {number_field}) of the forms P[OK+I], consisting of matrices with determinants that are totally positive units in OK, where OK is the ring of integers and I is {base_ideal}'
    ltx = 'P[OK + I]'.format(degree, latex(number_field))
    return ExtendedHilbertModularGroup_class(base_ideal=base_ideal, sage_name=name, latex_string=ltx)


class ExtendedHilbertModularGroup_class(LinearMatrixGroup_generic):
    r"""
    Class for Extended Hilbert modular groups, here defined as either P[OK + I] (default) with determinant that are totally positive units in OK.
    """

    Element = ExtendedHilbertModularGroupElement

    def __init__(self, base_ideal, sage_name, latex_string):
        r"""
         Init a Extended Hilbert modular group  of the form P[OK+I], where OK is the ring of integers and I is the base_ideal

        INPUT:

        - ``base_ideal`` - NumberFieldFractionalIdeal
        - ``sage_name`` - string
        - ``latex_string`` - string

        EXAMPLES::
            sage: from extended_hilbert_modgroup.extended_hilbert_modular_group_class import *
            sage: number_field = QuadraticField(5)
            sage: base_ideal = number_field.different()
            sage: ltx = 'P[OK + I]'.format(2, latex(number_field))
            sage: name = f"Extended Hilbert modular group of order 2 (over {number_field}) of the forms P[OK+I], where I is {base_ideal}"
            sage: ExtendedHilbertModularGroup_class(base_ideal=base_ideal,sage_name=name,latex_string=ltx)
            Extended Hilbert modular group of order 2 (over Number Field in a with defining polynomial x^2 - 5 with a = 2.236067977499790?) of the forms P[OK+I], where I is Fractional ideal (-a)
            sage: H1=ExtendedHilbertModularGroup(5)
            sage: TestSuite(H1).run()
            sage: H1(1)
            [1 0]
            [0 1]
            sage: H1([1,1,0,1])
            [1 1]
            [0 1]
            sage: H1([1,H1.base_ideal().gens()[0],0,1])
            [1 5]
            [0 1]

        """
        # Instance data related to the field and ideal
        self._base_ideal = base_ideal
        self._OK = base_ideal.number_field().ring_of_integers()
        # Instance data related to cusps
        self._ncusps = None
        self._cusps = []
        self._ideal_cusp_representatives = []
        self._cusp_normalizing_maps = {}
        self._cusp_normalizing_maps_inverse = {}
        # At the moment we only deal with full level (1)
        self._level = self._OK.fractional_ideal(1)
        super(ExtendedHilbertModularGroup_class, self).__init__(degree=Integer(2), base_ring=self.number_field(),
                                                                special=False,
                                                                sage_name=sage_name,
                                                                latex_string=latex_string,
                                                                category=Groups().Infinite(),
                                                                invariant_form=None)

    def OK(self):
        """
        Return the ring of integers associated to self.

        EXAMPLES::

            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: H = ExtendedHilbertModularGroup(5)
            sage: H.OK()
        """
        return self._OK

    def number_field(self):
        """
        Return the number field associated to self.

        EXAMPLES::

            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: H = ExtendedHilbertModularGroup(5)
            sage: H.number_field()
            Number Field in a with defining polynomial x^2 - 5 with a = 2.236067977499790?
        """
        return self.base_ideal().number_field()

    def base_ideal(self):
        """
        Return the base_ideal associated to self.

        EXAMPLES::

            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: H = ExtendedHilbertModularGroup(5)
            sage: H.base_ideal()
            Fractional ideal (1)
        """
        return self._base_ideal

    def generators(self, algorithm='standard'):
        r"""
        Return a list of generators of ``self``.

        INPUT:

        - ``algorithm`` (string) either 'standard' or 'elementary'.

        If 'elementary' is given return a set of generators
        consisting of elementary (i.e. upper- and lower-triangular) matrices.
        Otherwise return a set of reflections and translations.

        EXAMPLES::

            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: H = ExtendedHilbertModularGroup(3)
            sage: H.generators()
            [
             [1 0]  [-a + 2      0]  [ 0 -1]  [1 1]  [1 a]
             [0 1], [     0      1], [ 1  0], [0 1], [0 1]
            ]

            sage: H.generators(algorithm ='elementary')
            [
             [1 0]  [-a + 2      0]  [1 0]  [1 0]  [1 1]  [1 a]
             [0 1], [     0      1], [1 1], [a 1], [0 1], [0 1]
            ]

        """
        number_field = self.base_ideal().number_field()
        degree = number_field.degree()
        fundamental = UnitGroup(number_field).gens_values()
        gens = []
        for x in fundamental:
            if x.is_totally_positive():
                gens.append(self.E(x))
            elif (-x).is_totally_positive():
                gens.append(self.E(-x))
            else:
                gens.append(self.E(x ** 2))
        if algorithm == 'standard':
            gens.append(self.S())
            if self.base_ideal() == self.OK().fractional_ideal(1):
                for x in self.OK().basis():
                    gens.append(self.T(x))
            else:
                for x in self.base_ideal().basis():
                    gens.append(self.T(x))
                for x in self.base_ideal().inverse().basis():
                    gens.append(self.T(x))
        elif algorithm == 'elementary':
            for x in self.base_ideal().basis():
                gens.append(self.L(x))
            for x in self.base_ideal().inverse().basis():
                gens.append(self.T(x))
        else:
            raise ValueError("Unknown algorithm '{0}'. Expected one of 'standard' or 'elementary'")
        return gens

    @cached_method
    def S(self):
        """
        Return the element S = ( 0 & -1 // 1 & 0 ) of self.

        EXAMPLES::

            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: ExtendedHilbertModularGroup(5).S()
            [ 0 -1]
            [ 1  0]
            sage: ExtendedHilbertModularGroup(10).S()
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

            sage: from hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: H = ExtendedHilbertModularGroup(5)
            sage: H.T()
            [1 1]
            [0 1]
            sage: u0,u1=H.number_field().unit_group().gens()
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

    def ideal(self, x: tuple):
        base_ideal = self.base_ideal()
        return ideal_wrt_base_ideal(base_ideal, x)

    def ngens(self, algorithm='standard'):
        r"""
        Return the number of generators of self as given by the function 'gens'.

        INPUT:

        - ``algorithm`` -- string (default='standard') give the algorithm to compute the generators

        EXAMPLES::

            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: ExtendedHilbertModularGroup(5).ngens()
            5

        """
        return len(self.generators(algorithm))

    def gen(self, i):
        r"""
        Return the i-th generator of self, i.e. the i-th element of the
        tuple self.gens().

        EXAMPLES::

            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: ExtendedHilbertModularGroup(5).gen(1)
            [-1/2*a + 3/2            0]
            [           0            1]
        """
        return self.generators()[i]

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

    def level(self):
        """
        Return the level of this Extended Hilbert modular group (currently only (1))

        EXAMPLES::

            sage: from hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: ExtendedHilbertModularGroup(5).level()
            Fractional ideal (1)

        """
        return self._level

    def ncusps(self):
        """
        Return the number of inequivalent cusp for the action of Extended Hilbert Modular group
        on the n-copies of upper half-plane.

        EXAMPLES::

            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: H1=ExtendedHilbertModularGroup(5)
            sage: H1.ncusps()
            1

            sage: H2=ExtendedHilbertModularGroup(10)
            sage: H2.ncusps()
            2

            sage: var('x')
            x
            sage: K = NumberField(x^3-36*x-1, names='a')
            sage: H3=ExtendedHilbertModularGroup(K)
            sage: H3.ncusps()
            5

            sage: K4 = NumberField(x**4 - 17*x**2 + 36,names='a'); a=K4.gen()
            sage: H4=ExtendedHilbertModularGroup(K4)
            sage: H4.ncusps()
            2
        """
        if not self._ncusps:
            self._ncusps = self.OK().class_number()
        return self._ncusps

    @cached_method
    def cusps(self):
        """
        A set of cusp representatives of self.


        EXAMPLES::

            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: H1=ExtendedHilbertModularGroup(5)
            sage: H1.cusps()
            [Cusp Infinity of Number Field in a with defining polynomial x^2 - 5 with a = 2.236067977499790? with respect to the base ideal
            Fractional ideal (1)]

            sage: H2=ExtendedHilbertModularGroup(10)
            sage: H2.cusps()
            [Cusp Infinity of Number Field in a with defining polynomial x^2 - 10 with a = 3.162277660168380? with respect to the base ideal Fractional ideal (1),
            Cusp [2: a] of Number Field in a with defining polynomial x^2 - 10 with a = 3.162277660168380? with respect to the base ideal Fractional ideal (1)]
            sage: x=var('x')
            sage: K = NumberField(x^3-36*x-1, names='a')
            sage: H3=ExtendedHilbertModularGroup(K); H3
            Hilbert Modular Group ... x^3 - 36*x - 1
            sage: H3.cusps()
            [Cusp Infinity of Number Field in a with defining polynomial x^3 - 36*x - 1 with respect to the base ideal Fractional ideal (1),
             Cusp [2: a + 1] of Number Field in a with defining polynomial x^3 - 36*x - 1 with respect to the base ideal Fractional ideal (1),
             Cusp [3: 1/3*a^2 + 1/3*a - 26/3] of Number Field in a with defining polynomial x^3 - 36*x - 1 with respect to the base ideal Fractional ideal (1),
             Cusp [2: 1/3*a^2 + 1/3*a - 23/3] of Number Field in a with defining polynomial x^3 - 36*x - 1 with respect to the base ideal Fractional ideal (1),
             Cusp [6: 1/3*a^2 + 1/3*a - 26/3] of Number Field in a with defining polynomial x^3 - 36*x - 1 with respect to the base ideal Fractional ideal (1)]

            sage: K4 = NumberField(x**4 - 17*x**2 + 36,names='a'); a=K4.gen()
            sage: H4=ExtendedHilbertModularGroup(NumberField(x**4 - 17*x**2 + 36,names='a'))
            sage: H4.cusps()
            [Cusp Infinity of Number Field in a with defining polynomial x^4 - 17*x^2 + 36 with respect to the base ideal Fractional ideal (1),
             Cusp [2: a + 1] of Number Field in a with defining polynomial x^4 - 17*x^2 + 36 with respect to the base ideal Fractional ideal (1)]


        """
        if not self._cusps:
            self._cusps = []
            for a in self.ideal_cusp_representatives():
                logger.debug("Set cusp info for ideal a={0}".format(a))
                if a.is_trivial():
                    ca = NFCusp_wrt_base_ideal(self.base_ideal(), self.OK()(1), self.OK()(0),
                                               lreps=self.ideal_cusp_representatives())
                else:
                    ag = gens_reduced_wrt_base_ideal(self.base_ideal(), a)
                    ca = NFCusp_wrt_base_ideal(self.base_ideal(), ag[0], ag[1], lreps=self.ideal_cusp_representatives())
                self._cusps.append(ca)
                if ca.ideal() != a:
                    raise ArithmeticError("Failed to associate a cusp to ideal {0}".format(a))
        return self._cusps

    def ideal_cusp_representatives(self):
        r"""
        Return a list of ideals corresponding to cusp representatives, i.e.
        ideal representatives of ideal classes.

        Note: We choose an ideal of smallest norm in each class.
            If the ideal given by sage is already minimal we return this.

        EXAMPLES::

            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: H1=ExtendedHilbertModularGroup(5)
            sage: H1.ideal_cusp_representatives()
            [Fractional ideal (1)]

            sage: H2=ExtendedHilbertModularGroup(10)
            sage: H2.ideal_cusp_representatives()
            [Fractional ideal (1), Fractional ideal (2, a)]

            sage: K.<a> = QuadraticField(10)
            sage: base_ideal = K.fractional_ideal(2, a)
            sage: H2=HilbertModularGroup(base_ideal)
            sage: H2.ideal_cusp_representatives()
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

    def cusp_representative(self, cusp, return_map=False):
        r"""
        Return a representative cusp and optionally a corresponding map.

        INPUT:
        - ``cusp`` -- cusp
        - ``return_map`` -- bool (default: False)
                            Set to True to also return the map giving the equivalence.

        EXAMPLES::

            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: H1=ExtendedHilbertModularGroup(10)
            sage: c = NFCusp_wrt_base_ideal(H1.base_ideal(), 0, 1)
            sage: H1.cusp_representative(c)
            Cusp Infinity of Number Field in a with defining polynomial x^2 - 10 with a = 3.162277660168380? with respect to the base ideal Fractional ideal (1)

            sage: K.<a>=QuadraticField(10)
            sage: base_ideal = K.fractional_ideal(2, a)
            sage: H2=ExtendedHilbertModularGroup(base_ideal)
            sage: c = NFCusp_wrt_base_ideal(base_ideal, 0, 1)
            sage: H2.cusp_representative(c)
            Cusp [2: 2] of Number Field in a with defining polynomial x^2 - 10 with a = 3.162277660168380? with respect to the base ideal Fractional ideal (2, a)

            sage: a = H2.number_field().gen()
            sage: x,y = 3*a - 10, a - 4
            sage: c = NFCusp_wrt_base_ideal(base_ideal, x, y)
            sage: H2.cusp_representative(c)
            Cusp Infinity of Number Field in a with defining polynomial x^2 - 10 with a = 3.162277660168380? with respect to the base ideal Fractional ideal (2, a)


        """
        for c in self.cusps():
            if return_map:
                t, B = cusp.is_Gamma0_wrt_base_ideal_equivalent(c, self.level(), Transformation=True)
                if t:
                    return c, self(B)
            else:
                t = cusp.is_Gamma0_wrt_base_ideal_equivalent(c, self.level())
                if t:
                    return c
        raise ArithmeticError(f"Could not find cusp representative for {cusp}")

    def cusp_normalizing_map(self, cusp, inverse=False, check=False):
        r"""
        Given a cusp (a:c) Return a matrix A = [[ a ,b ], [c , d]] in SL(2,K) such that
        A(Infinity)=(a:c) and b, d in self.base_ring().ideal(a,c)**-1

        INPUT:

        - ``cusp`` -- Instance of NFCusp
        - ``inverse`` -- bool (default: False) set to True to return the inverse map
        - ``check`` -- bool (default: False) set to True to check the result

        If inverse = True then return A^-1

        EXAMPLES::

            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: K.<a> = QuadraticField(3)
            sage: base_ideal = K.fractional_ideal(2)
            sage: H1=ExtendedHilbertModularGroup(base_ideal)
            sage: H1.cusp_normalizing_map(H1.cusps()[0])
            [1 0]
            [0 1]
            sage: H1.cusp_normalizing_map(NFCusp_wrt_base_ideal(H1.base_ideal(), 5, 1))
            [ 5 -1]
            [ 1  0]

            sage: K.<a> = QuadraticField(10)
            sage: base_ideal = K.fractional_ideal(2, a)
            sage: H2=ExtendedHilbertModularGroup(base_ideal)
            sage: H2.cusp_normalizing_map(H2.cusps()[1])
            [   2 -1/2]
            [   2    0]

        """
        base_nf = self.number_field()
        if not isinstance(cusp, NFCusp_wrt_base_ideal) or cusp.number_field() != base_nf:
            raise ValueError(f"Input should be a NF cusp defined over {base_nf}!")
        ca, cb = (cusp.numerator(), cusp.denominator())
        if not (ca, cb) in self._cusp_normalizing_maps:
            # First find the equivalent representative
            # crep, B = self.cusp_representative(cusp,return_map=True)
            # crepa,crepb = crep.numerator(),crep.denominator()
            # crep_normalizing_map = self._cusp_normalizing_maps.get((crepa,crepb))
            # if not crep_normalizing_map:
            # Find a normalizing map of the cusp representative
            a, b, c, d = cusp.ABmatrix_wrt_base_ideal()
            det = a * d - b * c
            A = Matrix(self.number_field(), 2, 2, [a, b / det, c, d / det])
            # A = B.matrix().inverse()*crep_normalizing_map
            if check:
                infinity = NFCusp_wrt_base_ideal(self.base_ideal(), 1, 0)
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
        Apply the cusp normalising map associated with the cusp to an element z

        INPUT:

        - `cusp` - an instance of NFcusp_wrt_base_ideal
        - `z` - an element in
                 - the base number field
                 - the set fo cusps wrt base_ideal
                 -  in ComplexPlaneProductElement__class
        - `inverse` - set to True if applying the inverse map

        EXAMPLES::

            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup,ComplexPlaneProductElement
            sage: H2=ExtendedHilbertModularGroup(10)
            sage: H2.apply_cusp_normalizing_map(H2.cusps()[1],1.0)
            0.360379610028063
            sage: H2.apply_cusp_normalizing_map(H2.cusps()[1],1)
            1/6*a - 1/6
            sage: z = NFCusp_wrt_base_ideal(H2.base_ideal(), 1)
            sage: H2.apply_cusp_normalizing_map(H2.cusps()[1],z)
            Cusp [a - 1: 6] of Number Field in a with defining polynomial x^2 - 10 with a = 3.162277660168380? with respect to the base ideal Fractional ideal (1)
            sage: a=H2.OK().gens()[1]
            sage: H2.apply_cusp_normalizing_map(H2.cusps()[1],a)
            3/16*a
            sage: z=ComplexPlaneProductElement([CC(1,0),CC(1,0)]); z
            [1.00000000000000, 1.00000000000000]
            sage: H2.apply_cusp_normalizing_map(H2.cusps()[1],z)
            [-0.693712943361397, 0.360379610028063]
            sage: H2.apply_cusp_normalizing_map(H2.cusps()[1],1).complex_embeddings()
            [-0.693712943361397, 0.360379610028063]

        """
        a, b, c, d = self.cusp_normalizing_map(cusp, inverse=inverse).list()
        if z == infinity:
            return a / c
        number_field = self.number_field()
        if isinstance(z, NFCusp_wrt_base_ideal) and z.number_field() == number_field:
            return z.apply([a, b, c, d])
        if z in number_field:
            return (a * z + b) / (c * z + d)
        if isinstance(z, ComplexPlaneProductElement__class) and \
                z.degree() == number_field.absolute_degree():
            return z.apply(matrix(2, 2, [a, b, c, d]))
        raise ValueError("Unsupported type for action with cusp normalizer! (z={0})".format(z))