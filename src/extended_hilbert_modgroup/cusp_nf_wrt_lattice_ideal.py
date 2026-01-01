from sage.modules.free_module_element import vector
from sage.rings.real_mpfr import RR
from sage.rings.complex_mpfr import ZZ
from sage.structure.element import Element
from sage.structure.richcmp import richcmp, rich_to_bool
from sage.modular.cusps_nf import NFCusps, NFCusp
from sage.modular.cusps_nf import list_of_representatives
import itertools
from sage.matrix.constructor import Matrix
from sage.coding.kasami_codes import GF

class NFCusp_wrt_lattice_ideal(Element):
    r"""
    Create a number field cusp, i.e., an element of `\mathbb{P}^1(k)` with respect to a lattice_ideal.
    In a standard cusp for a field the lattice_ideal is OK. Ideally they are same but the ideal
    represented by them differs. Moreover, the GHMatrix for the cusp will be different.
    parent - NFCusps.
    INPUT:

    - ``lattice_ideal`` -- the ideal of a number field over which the cusp is defined.

    - ``a`` -- it can be a number field element (integral or not), or
      a number field cusp.

    - ``b`` -- (optional) when present, it must be either Infinity or
      coercible to an element of the number field.

    - ``lreps`` -- (optional) a list of chosen representatives for all the
      ideal classes of the field. When given, the representative of the cusp
      will be changed so its associated ideal is one of the ideals in the list.

    OUTPUT:

    ``[a: b]`` -- a number field cusp with respect to the lattice_ideal I.

    EXAMPLES::
        sage: from extended_hilbert_modgroup.all import NFCusp_wrt_lattice_ideal
        sage: K.<a> = QuadraticField(2)
        sage: lattice_ideal = K.fractional_ideal(1)
        sage: NFCusp_wrt_lattice_ideal(lattice_ideal, a, 2)
        Cusp [a: 2] of Number Field in a with defining polynomial x^2 - 2 with a = 1.414213562373095? with
        respect to  lattice_ideal
        sage: lattice_ideal = K.different()
        sage: NFCusp_wrt_lattice_ideal(lattice_ideal, a, 2)
        Cusp [a: 2] of Number Field in a with defining polynomial x^2 - 2 with a = 1.414213562373095? with
        respect to  lattice_ideal
        sage: NFCusp_wrt_lattice_ideal(lattice_ideal, 0)
        Cusp [0: 1] of Number Field in a with defining polynomial x^2 - 2 with a = 1.414213562373095? with
        respect to  lattice_ideal
        sage: NFCusp_wrt_lattice_ideal(lattice_ideal, a+5, 0)
        Cusp Infinity of Number Field in a with defining polynomial x^2 - 2 with a = 1.414213562373095? with
        respect to lattice_ideal
        sage: I = K.fractional_ideal(a)
        sage: NFCusp_wrt_lattice_ideal(lattice_ideal, a+5, 2, lreps = [I])
        Cusp [2*a + 10: 4] of Number Field in a with defining polynomial x^2 - 2 with a = 1.414213562373095? with
        respect to  lattice_ideal
        sage: (2*a+10)*K.fractional_ideal(1) + 4*(lattice_ideal.inverse()) == I
        True
        sage: K.<a> = QuadraticField(3)
        sage: K.<a> = QuadraticField(10)
        sage: lattice_ideal = K.fractional_ideal(2)
        sage: lreps = [K.fractional_ideal(1), K.fractional_ideal(2, a)]
        sage: NFCusp_wrt_lattice_ideal(lattice_ideal, a+1, a, lreps = lreps)
        Cusp [2*a + 2: 2*a] of Number Field in a with defining polynomial x^2 - 10 with a = 3.162277660168380? with
        respect to  lattice_ideal
        sage: from extended_hilbert_modgroup.cusp_nf_wrt_lattice_ideal import ideal_wrt_lattice_ideal
        sage: ideal_wrt_lattice_ideal(lattice_ideal, (2*a+2, 2*a)) in lreps
        True
    """

    def __init__(self, lattice_ideal, a, b = None, parent = None, lreps = None):
        self._lattice_ideal = lattice_ideal
        self._number_field = lattice_ideal.number_field()
        self._OK = lattice_ideal.number_field().OK()
        if parent is None:
            parent = NFCusps(self._number_field)
        Element.__init__(self, parent)
        K = self._number_field
        R = self._OK
        if isinstance(a, NFCusp_wrt_lattice_ideal):
            if a.parent() == parent:
                self.__a = R(a.__a)
                self.__b = R(a.__b)
            else:
                raise ValueError("Cannot coerce cusps from one field to another")
        elif not a:
            if b is None:
                self.__a = R.zero()
                self.__b = R.one()
            elif b in R:
                self.__a = R.zero()
                self.__b = R(b)
            else:
                self.__a = R.zero
                self.__b = K(a)
        elif b is None:
            self.__a = R.one()
            self.__b = R.zero()
        else:
            cusp = NFCusp(K, a, b)
            self.__a = cusp.numerator()
            self.__b = cusp.denominator()
        if lreps is not None:
            I = self.ideal()
            for J in lreps:
                if (J / I).is_principal():
                    newI = J
            l = (newI / I).gens_reduced()[0]
            a = self.OK()(l * self.__a)
            b = self.OK()(l * self.__b)
            cusp = NFCusp_wrt_lattice_ideal(lattice_ideal, a, b)
            self.__a = cusp.numerator()
            self.__b = cusp.denominator()

    def _repr_(self):
        """
        String representation of this cusp.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_lattice_ideal
            sage: K.<a> = QuadraticField(3)
            sage: lattice_ideal = K.different()
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, a, 2)
            sage: c
            Cusp [a: 2] of Number Field in a with defining polynomial x^2 - 3 with a = 1.732050807568878?
            with respect to  lattice_ideal
            sage: c._repr_()
            'Cusp [a: 2] of Number Field in a with defining polynomial x^2 - 3 with a = 1.732050807568878? with respect to  lattice_ideal'
        """
        if self.__b.is_zero():
            return "Cusp Infinity of %s with respect to lattice_ideal" % (
                self.parent().number_field())
        else:
            return "Cusp [%s: %s] of %s with respect to  lattice_ideal" % (self.__a, self.__b,
                                                                                 self.parent().number_field())

    def lattice_ideal(self):
        """
        Return the lattice_ideal associated to the cusp.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_lattice_ideal
            sage: K.<a> = QuadraticField(3)
            sage: lattice_ideal = K.fractional_ideal(a)
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, a, 2)
            sage: c.lattice_ideal()
            Fractional ideal (a)
        """
        return self._lattice_ideal

    def OK(self):
        """
        Return the ring of integers of the number field associated to the cusp.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_lattice_ideal
            sage: K = NumberField(x^3-36*x-1, names = 'a')
            sage: K.<a> = NumberField(x^3-36*x-1)
            sage: lattice_ideal = K.fractional_ideal(2)
            sage: lattice_ideal = K.fractional_ideal(a)
            sage: K.<a> = NumberField(x^3-36*x-1)
            sage: lattice_ideal = K.fractional_ideal(a)
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, a, 2)
            sage: c.OK()
            Maximal Order generated by [1/3*a^2 + 1/3*a + 1/3, a] in Number Field in a with defining polynomial x^3 - 36*x - 1
        """
        return self._OK

    def number_field(self):
        """
        Return the number field associated to the cusp.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_lattice_ideal
            sage: K4.<a> = NumberField(x^4-17*x**2+36)
            sage: lattice_ideal = K4.fractional_ideal(a)
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, a, 2)
            sage: c.number_field()
            Number Field in a with defining polynomial x^4 - 17*x^2 + 36

        """
        return self.parent().number_field()

    def is_infinity(self):
        """
        Return ``True`` if this is the cusp infinity.

        EXAMPLES::
           sage: from extended_hilbert_modgroup.all import NFCusp_wrt_lattice_ideal
           sage: K1.<a> = QuadraticField(2)
           sage: lattice_ideal = K1.fractional_ideal(a)
           sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, a, 2)
           sage: c.is_infinity()
           False
           sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, 0)
           sage: c.is_infinity()
           False
           sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, a, 0)
           sage: c.is_infinity()
           True
           sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, (a, 0))
           sage: c.is_infinity()
           True

        """
        return self.__b == 0

    def numerator(self):
        """
        Return the numerator of the cusp ``self``.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_lattice_ideal
            sage: K1.<a> = QuadraticField(2)
            sage: lattice_ideal = K1.fractional_ideal(a)
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, a/2, (a**2+a)/a)
            sage: c.numerator()
            -a + 2
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, 2, 6)
            sage: c.numerator()
            2
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, oo)
            sage: c.numerator()
            1
        """
        return self.__a

    def denominator(self):
        """
        Return the numerator of the cusp ``self``.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_lattice_ideal
            sage: K2.<a> = QuadraticField(5)
            sage: lattice_ideal = K2.fractional_ideal(2)
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, a, 2)
            sage: c.denominator()
            2
            sage: d = NFCusp_wrt_lattice_ideal(lattice_ideal, 1, a)
            sage: d.denominator()
            a
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, oo)
            sage: c.denominator()
            0
        """
        return self.__b

    def _number_field_element_(self):
        """
        Coerce to an element of the number field.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_lattice_ideal
            sage: K1.<a> = QuadraticField(2)
            sage: lattice_ideal = K1.fractional_ideal(2)
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, a, 2)
            sage: c._number_field_element_()
            1/2*a
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, 1, a+1)
            sage: c._number_field_element_()
            a - 1
        """
        if self.__b.is_zero():
            raise TypeError("%s is not an element of %s" % (self, self.number_field()))
        K = self.number_field()
        return K(self.__a / self.__b)

    def _ring_of_integers_element_(self):
        """
        Coerce to an element of the ring of integers of the number field.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_lattice_ideal
            sage: K3.<a> = QuadraticField(3)
            sage: lattice_ideal = K3.fractional_ideal(2)
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, a+1, 1)
            sage: c._ring_of_integers_element_()
            a + 1
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, 1, a+1)
            sage: c._ring_of_integers_element_()
            Traceback (most recent call last):
            ...
            TypeError: Cusp [1: a + 1] of Number Field in a with defining polynomial x^2 - 3 with
            a = 1.732050807568878? with respect to  lattice_ideal is not an integral element
        """
        if self.__b.is_one():
            return self.__a
        R = self.OK()
        if self.__b.is_zero():
            raise TypeError("%s is not an element of %s" % (self, R))
        try:
            return R(self.__a / self.__b)
        except (ValueError, TypeError):
            raise TypeError("%s is not an integral element" % self)

    def _latex_(self):
        r"""
        Return the representation of this cusp.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_lattice_ideal
            sage: K4.<a> = QuadraticField(10)
            sage: lattice_ideal = K4.different()
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, 3*a, a+1)
            sage: latex(c)
            \[3 \sqrt{10}: \sqrt{10} + 1\]
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, oo)
            sage: latex(c)
            \infty
        """
        if self.__b.is_zero():
            return "\\infty"
        else:
            return "\\[%s: %s\\]" % (self.__a._latex_(),
                                     self.__b._latex_())

    def _richcmp_(self, right, op):
        """
        Compare the cusps ``self`` and ``right``.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_lattice_ideal
            sage: K4.<a> = QuadraticField(10)
            sage: lattice_ideal = K4.fractional_ideal(2)
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, a, 2)
            sage: d = NFCusp_wrt_lattice_ideal(lattice_ideal, oo)
            sage: c < d
            True
            sage: NFCusp_wrt_lattice_ideal(lattice_ideal, oo) < c
            False
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, 2/3)
            sage: d = NFCusp_wrt_lattice_ideal(lattice_ideal, 4/5)
            sage: c < d
            True
        """
        if self.__b.is_zero():
            if right.denominator().is_zero():
                return rich_to_bool(op, 0)
            else:
                return rich_to_bool(op, 1)
        else:
            if right.denominator().is_zero():
                return rich_to_bool(op, -1)
            else:
                return richcmp(self._number_field_element_(),
                               right._number_field_element_(), op)

    def __neg__(self):
        """
        Return the negative of this cusp.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_lattice_ideal
            sage: K2.<a> = QuadraticField(5)
            sage: lattice_ideal = K2.fractional_ideal(2)
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, a, a+1)
            sage: c.__neg__()
            Cusp [-a: a + 1] of Number Field in a with defining polynomial x^2 - 5 with a = 2.236067977499790?
            with respect to  lattice_ideal
        """
        return NFCusp_wrt_lattice_ideal(self.lattice_ideal(), -self.__a, self.__b)

    def apply(self, g):
        """
        Return g(``self``), where ``g`` is a 2x2 Matrix.

        INPUT:

        - ``g`` -- a list of  [a, b, c, d]. They are
          entries of a 2x2 matrix.

        OUTPUT:

        A number field cusp, obtained by the action of ``g`` on the cusp
        ``self``.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_lattice_ideal
            sage: K4.<a> = QuadraticField(10)
            sage: lattice_ideal = K4.different()
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, 0, 1)
            sage: c.apply([0, -1, 1, 0])
            Cusp Infinity of Number Field in a with defining polynomial x^2 - 10 with a = 3.162277660168380?
            with respect to lattice_ideal
            sage: c.apply([1, a, 0, 1])
            Cusp [a: 1] of Number Field in a with defining polynomial x^2 - 10 with a = 3.162277660168380?
            with respect to  lattice_ideal
        """
        return NFCusp_wrt_lattice_ideal(self.lattice_ideal(), g[0] * self.__a + g[1] * self.__b,
                                        g[2] * self.__a + g[3] * self.__b)

    def ideal(self):
        """
        Return the ideal associated to the cusp ``self``.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_lattice_ideal
            sage: K3.<a> = QuadraticField(3)
            sage: lattice_ideal = K3.fractional_ideal(2)
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, 3, a-1)
            sage: c.ideal()
            Fractional ideal (-1/2*a + 1/2)
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, oo)
            sage: c.ideal()
            Fractional ideal (1)
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, (a+1)/(a-1), a+1)
            sage: c.ideal()
            Fractional ideal (-1/2*a + 1/2)
        """
        return ideal_wrt_lattice_ideal(self.lattice_ideal(), (self.__a, self.__b))

    def GHmatrix_wrt_lattice_ideal(self, return_H = False):
        """
        Return GH-matrix associated with the cusp ``self``.

        EXAMPLES:

        ::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_lattice_ideal
            sage: K3.<a> = QuadraticField(3)
            sage: lattice_ideal = K3.fractional_ideal(2)
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, oo)
            sage: c.GHmatrix_wrt_lattice_ideal()
            [1, 0, 0, 1]

        ::

            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, 0)
            sage: c.GHmatrix_wrt_lattice_ideal()
            [0, -1, 1, 0]

        Note that the GH-matrix associated to a cusp is not unique, and the
        output of the ``GHmatrix`` function may change.

        ::

            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, 3/2, a-1)
            sage: M = c.GHmatrix_wrt_lattice_ideal()
            sage: M
            [3*a + 3, 1, 4, a - 1]
            sage: M[0] == c.numerator() and M[2] == c.denominator()
            True
            sage: M[2] in lattice_ideal*c.ideal()
            True
            sage: NFCusp_wrt_lattice_ideal(lattice_ideal, oo).apply(M)
            Cusp [3*a + 3: 4] of Number Field in a with defining polynomial x^2 - 3 with a = 1.732050807568878?
            with respect to  lattice_ideal
            sage: NFCusp_wrt_lattice_ideal(lattice_ideal, oo).apply(M) == c
            True
            sage: (M[0]*M[3] - M[1]*M[2]).is_totally_positive()
            True

        ::
            sage: K4.<a> = QuadraticField(10)
            sage: lattice_ideal = K4.fractional_ideal(2, a)
            sage: c = NFCusp_wrt_lattice_ideal(lattice_ideal, 3/2, a-1)
            sage: M = c.GHmatrix_wrt_lattice_ideal()
            sage: M
            [a + 1, -5/2*a - 7, 6, -2*a - 11]
            sage: (M[0]*M[3] - M[1]*M[2]).is_totally_positive()
            True
            sage: M[0] == c.numerator() and M[2] == c.denominator()
            True
            sage: M[2] in lattice_ideal*c.ideal()
            True
            sage: NFCusp_wrt_lattice_ideal(lattice_ideal, oo).apply(M) == c
            True

        """
        K = self.number_field()
        G = self.ideal()
        if G.is_principal():
            H = G
            g = (G * H).gens_reduced()[0]
        else:
            H = K.fractional_ideal((G.gens_reduced()[1]) ** 2) / G
            g = G.gens_reduced()[1]**2
        assert (G * H).is_principal()
        a1 = self.__a
        a2 = self.__b
        #g = (G * H).gens_reduced()[0]
        if self.is_infinity():
            H = K.OK().fractional_ideal(1)
            if return_H:
                return [1, 0, 0, 1], H
            else:
                return [1, 0, 0, 1]
        if not self:
            assert -g/self.__b in (self.lattice_ideal().inverse() * H)
            #gens = gens_reduced_wrt_lattice_ideal(self.lattice_ideal(), self.lattice_ideal() * G)[1]
            if return_H:
                return [self.__a, -g /self.__b, self.__b, 0], H
            else:
                return [self.__a, -g / self.__b, self.__b, 0]
        Ginv = G ** (-1)
        A1 = a1 * Ginv
        A2 = a2 * (self.lattice_ideal().inverse()) * Ginv
        r = A1.element_1_mod(A2)
        b1 = -(1 - r) / a2 * g
        b2 = (r / a1) * g
        GHM = [a1, b1, a2, b2]
        if return_H:
            return GHM, H
        else:
            return GHM

    def is_Gamma0_wrt_lattice_ideal_equivalent(self, other, N, tp_units = True, Transformation = False):
        r"""
        Check if cusps ``self`` and ``other`` are `\Gamma_0(N)_wrt_lattice_ideal`- equivalent.

        INPUT:
        - ``other`` -- a number field cusp wrt lattice_ideal or a list of two number field
          elements which define a cusp wrt lattice_ideal.

        - `` N `` -- an ideal of the number field (level)

        - `` tp_units `` -- True if we considering group with totally positive determinant otherwise False
                if the determinant is 1.

        - `` Transformation `` True if we want the matrix when the cusps are equivalent otherwise False.


        OUTPUT:

        - bool -- `` True `` if the cusps are equivalent.

        - a transformation matrix -- (if ``Transformation=True``) a list of
          integral elements [a, b, c, d] which are the entries of a 2x2 matrix
          M in `\Gamma_0(N) wrt lattice_ideal` such that M * ``self`` = ``other`` if ``other``
          and ``self`` are `\Gamma_0(N)`- equivalent. If ``self`` and ``other``
          are not equivalent it returns zero.

        EXAMPLES:

        ::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_lattice_ideal
            sage: K3.<a> = QuadraticField(3)
            sage: lattice_ideal = K3.fractional_ideal(1)
            sage: level_ideal = K3.fractional_ideal(5)
            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: H3 = ExtendedHilbertModularGroup(K3, lattice_ideal, level_ideal)
            sage: H3.ncusps()
            2
            sage: H3.cusps()
            [Cusp [0: 1] of Number Field in a with defining polynomial x^2 - 3 with a = 1.732050807568878?
            with respect to  lattice_ideal, Cusp Infinity of Number Field in a with defining polynomial
            x^2 - 3 with a = 1.732050807568878? with respect to lattice_ideal]
            sage: t1 = NFCusp_wrt_lattice_ideal(lattice_ideal, 0, 1)
            sage: t2 = NFCusp_wrt_lattice_ideal(lattice_ideal, 1, 5)
            sage: t3 = NFCusp_wrt_lattice_ideal(lattice_ideal, 1, 0)
            sage: t3.is_Gamma0_wrt_lattice_ideal_equivalent(t1, level_ideal)
            False
            sage: t3.is_Gamma0_wrt_lattice_ideal_equivalent(t2, level_ideal)
            True
            sage: t3.is_Gamma0_wrt_lattice_ideal_equivalent(t2, level_ideal, Transformation = True)
            (True, [1, 0, 5, 1])
            sage: b, M = t3.is_Gamma0_wrt_lattice_ideal_equivalent(t2, level_ideal, Transformation = True)
            sage: t3.apply(M) == t2
            True

        ::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_lattice_ideal
            sage: K4.<a> = QuadraticField(10)
            sage: lattice_ideal = K4.fractional_ideal(1)
            sage: level_ideal = K4.fractional_ideal(7)
            sage: level_ideal.is_coprime(K4.discriminant())
            True
            sage: from extended_hilbert_modgroup.all import ExtendedHilbertModularGroup
            sage: H = ExtendedHilbertModularGroup(K4, lattice_ideal, level_ideal)
            sage: H.ncusps()
            4
            sage: t1, t2, t3, t4 = H.cusps()
            sage: t5 = NFCusp_wrt_lattice_ideal(lattice_ideal, 2, 3)
            sage: t5.is_Gamma0_wrt_lattice_ideal_equivalent(t1, level_ideal)
            True
            sage: b, M = t5.is_Gamma0_wrt_lattice_ideal_equivalent(t1, level_ideal, Transformation = True)
            sage: t5.apply(M) == t1
            True
        """
        K = self.number_field()
        other = NFCusp_wrt_lattice_ideal(self.lattice_ideal(), other)
        if not (self.ideal() / other.ideal()).is_principal():
            if not Transformation:
                return False
            else:
                return False, 0
        reps = list_of_representatives(N * self.lattice_ideal())
        alpha1 = NFCusp_wrt_lattice_ideal(self.lattice_ideal(), self, lreps = reps)
        alpha2 = NFCusp_wrt_lattice_ideal(self.lattice_ideal(), other, lreps = reps)
        delta = K.ideal(alpha1.__b) + N
        if (K.ideal(alpha2.__b) + N) != delta:
            if not Transformation:
                return False
            else:
                return False, 0
        M1, B1 = alpha1.GHmatrix_wrt_lattice_ideal(True)
        M2, B2 = alpha2.GHmatrix_wrt_lattice_ideal(True)
        A = alpha1.ideal()
        if B1 == B2:
            B = B1
        else:
            return 'B1 and B2 should be same'
        if M1 == [1, 0, 0, 1] or M2 == [1, 0, 0, 1]:
            if not Transformation:
                return True
            else:
                from sage.matrix.constructor import Matrix
                M = Matrix(K, 2, M1) * Matrix(K, 2, M2)
                if M1 == [1, 0, 0, 1]:
                    return True, M.list()
                else:
                    return True, M.inverse().list()
        GHdelta = A * B * delta * delta * self.lattice_ideal()
        units = units_mod_ideal(GHdelta, tp_units)
        for u in units:
            if (M2[2] * M1[3] - u * M1[2] * M2[3]) in GHdelta:
                if not Transformation:
                    return True
                else:
                    AuxCoeff = [1, 0, 0, 1]
                    Aux = M2[2] * M1[3] - u * M1[2] * M2[3]
                    if Aux in A * B * N * self.lattice_ideal():
                        if u != 1:
                            AuxCoeff[3] = u
                    else:
                        A1 = (A * B * N * self.lattice_ideal()) / GHdelta
                        A2 = B * K.fractional_ideal(M1[2] * M2[2]) / (A * self.lattice_ideal() * GHdelta)
                        f = A1.element_1_mod(A2)
                        w = ((1 - f) * Aux) / (M1[2] * M2[2])
                        AuxCoeff[3] = u
                        AuxCoeff[1] = w
                    from sage.matrix.constructor import Matrix
                    Maux = Matrix(K, 2, AuxCoeff)
                    M1inv = Matrix(K, 2, M1).inverse()
                    Mtrans = Matrix(K, 2, M2) * Maux * M1inv
                    assert Mtrans[1][0] in N
                    return True, Mtrans.list()
        if not Transformation:
            return False
        else:
            return False, 0

def gens_reduced_wrt_lattice_ideal(lattice_ideal, ideal):
    """
        Return the two generators (a, b) of the ideal in the sense, ideal= a*OK + b*(lattice_ideal.inverse())

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import gens_reduced_wrt_lattice_ideal
            sage: x = polygen(ZZ, 'x')
            sage: K.<a> = NumberField(x^2 - 5)
            sage: lattice_ideal = K.different()
            sage: ideal = K.fractional_ideal(3)
            sage: gens_reduced_wrt_lattice_ideal(lattice_ideal, ideal)
            (3, 0)
            sage: K1 = NumberField(x**4 - 17*x**2 + 36,names='a')
            sage: a = K1.gen()
            sage: lattice_ideal = K1.different()
            sage: ideal = K1.fractional_ideal(2, a)
            sage: gens_reduced_wrt_lattice_ideal(lattice_ideal, ideal)
            (2, 7/6*a^3 + 6*a^2 + 13/6*a - 51)
    """
    if not (lattice_ideal.number_field() == ideal.number_field()):
        return "lattice_ideal and ideal should be from the same ring of integers of a field"
    else:
        K = lattice_ideal.number_field()
        OK = K.OK()
        if lattice_ideal == OK.fractional_ideal(1):
            if ideal.is_principal():
                return tuple((ideal.gens_reduced()[0], 0))
            else:
                return ideal.gens_reduced()
        elif ideal.is_principal():
            a = ideal.gens_reduced()[0]
            return tuple((a, 0))
        else:
            a = ideal.gens_reduced()[0]
            temp = lattice_ideal * ideal
            if temp.is_principal():
                b = temp.gens_reduced()[0]
                return tuple((a, b))
            else:
                possible = list_of_representatives(ideal)
                for inverse in possible:
                    if (temp * inverse).is_principal():
                        b = temp * inverse
                return tuple((a, b.gens_reduced()[0]))


def ideal_wrt_lattice_ideal(lattice_ideal, x: tuple):
    """
        Return the ideal  in the sense, ideal = a*OK + b*(lattice_ideal.inverse())

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import (
            ....:  ideal_wrt_lattice_ideal,
            ....: gens_reduced_wrt_lattice_ideal
            ....: )
            sage: x = polygen(ZZ, 'x')
            sage: K.<a> = NumberField(x^2 - 5)
            sage: lattice_ideal=K.different()
            sage: ideal = K.fractional_ideal(3)
            sage: gens_reduced_wrt_lattice_ideal(lattice_ideal, ideal)
            (3, 0)
            sage: ideal_wrt_lattice_ideal(lattice_ideal, gens_reduced_wrt_lattice_ideal(lattice_ideal, ideal)) == ideal
            True
            sage: K1 = NumberField(x**4 - 17*x**2 + 36,names='a')
            sage: a=K1.gen()
            sage: lattice_ideal = K1.different()
            sage: ideal = K1.fractional_ideal(2, a)
            sage: gens_reduced_wrt_lattice_ideal(lattice_ideal, ideal)
            (2, 7/6*a^3 + 6*a^2 + 13/6*a - 51)
            sage: ideal_wrt_lattice_ideal(lattice_ideal, gens_reduced_wrt_lattice_ideal(lattice_ideal, ideal)) == ideal
            True
    """
    K = lattice_ideal.number_field()
    if x[1].is_zero():
        return K.OK().fractional_ideal(x[0])
    else:
        return x[0] * K.OK().fractional_ideal(1) + x[1] * (lattice_ideal.inverse())

def fundamental_unit_generator(K):
    """
    Return a list of fundamental units of the full unit group such that no unit in the list has all
    embeddings σ_i(x) negative.
    Example::
        sage: from extended_hilbert_modgroup.cusp_nf_wrt_lattice_ideal import fundamental_unit_generator
        sage: K2.<a> = QuadraticField(2)
        sage: fundamental_unit_generator(K2)
        [a + 1]
        sage: K4.<a> = NumberField(x**4 - 17*x**2 + 36)
        sage: fundamental_unit_generator(K4)
        [-1/12*a^3 + 11/12*a - 1/2,
         -1/12*a^3 + 23/12*a + 5/2,
        -1/6*a^3 - 1/2*a^2 + 7/3*a + 7]
        sage: K8.<a> = NumberField(x^3-36*x-1)
        sage: fundamental_unit_generator(K8)
        [a, a + 6]
    """
    generator = []
    for t in K.unit_group().fundamental_units():
        if all(phi(t) < 0 for phi in K.embeddings(RR)):
            t = -t
            generator.append(t)
        else:
            generator.append(t)
    return generator

def sign_matrix_real_field(K):
    """
    Compute the sign matrix of a totally real number field K.
    Rows = embeddings into RR
    Columns = generators (-1 and fundamental units)
    Example::
       sage: from extended_hilbert_modgroup.cusp_nf_wrt_lattice_ideal import sign_matrix_real_field
       sage: K2.<a> = QuadraticField(2)
       sage: sign_matrix_real_field(K2)
       [-1]
       [ 1]
       sage: K4.<a> = NumberField(x**4 - 17*x**2 + 36)
       sage: sign_matrix_real_field(K4)
       [ 1 -1  1]
       [-1 -1  1]
       [ 1  1  1]
       [-1  1 -1]
       sage: K8.<a> = NumberField(x^3-36*x-1)
       sage: sign_matrix_real_field(K8)
       [-1  1]
       [-1  1]
       [ 1  1]
    """
    gens = fundamental_unit_generator(K)
    embs = K.embeddings(RR)
    data = []
    for phi in embs:
        row = []
        for g in gens:
            val = phi(g)
            row.append(1 if val > 0 else -1)
        data.append(row)
    return Matrix(ZZ, data)


def totally_positive_unit_group_generators(K):
    """
    Return a list of n-1 generator of totally positive unit group. Here n is degree of extension of K over Q.
    Example::

        sage: from extended_hilbert_modgroup.cusp_nf_wrt_lattice_ideal import totally_positive_unit_group_generators
        sage: K2.<a> = QuadraticField(2)
        sage: totally_positive_unit_group_generators(K2)
        [2*a + 3]
        sage: K4.<a> = NumberField(x**4 - 17*x**2 + 36)
        sage: totally_positive_unit_group_generators(K4)
        [1/12*a^3 - 11/12*a + 3/2,
         -5/12*a^3 + 115/12*a + 27/2,
         -11/6*a^3 - 7/2*a^2 + 80/3*a + 51]
        sage: K3.<a> = QuadraticField(3)
        sage: totally_positive_unit_group_generators(K3)
        [-a + 2]
        sage: K10.<a> = QuadraticField(10)
        sage: totally_positive_unit_group_generators(K10)
        [-6*a + 19]
    """
    ulist = fundamental_unit_generator(K)
    n = len(ulist)
    vlist = list(itertools.product([0, 1], repeat = n))
    M = sign_matrix_real_field(K)
    M = M.apply_map(lambda x: 0 if x == 1 else 1).change_ring(GF(2))
    svectors = []
    for v in vlist:
        v = vector(GF(2), v)
        t = M * v
        if t.is_zero():
            svectors.append(v)
    V = svectors[0].parent()
    U = V.subspace(svectors)
    B = U.basis()
    BZ = [tuple(int(e) for e in v) for v in B]
    sq = [[2 if i == j else 0 for j in range(n)] for i in range(n)]
    for row in BZ:
        sq.append(list(row))
    E = Matrix(ZZ, sq)
    basis = E.row_module().basis()
    gen = []
    for v in basis:
        s = 1
        for i in range (0, n):
            s = s* ulist[i]**v[i]
        gen.append(s)
    return gen

def units_mod_ideal(I, tp_units = True):
    """
    Return the image of the totally positive unit group or the the squre of unit group inside quotient
    ring (O_K/I)^{*}

    Inputs:

    - `` I `` -            Ideal of a number field
    - `` tp_units`` -      True if we want to get the image of totally positive unit group False if we want
                           the image of square of the units.

    Output:
    A list of elements of invertible residues of O_K/I which are the image of totally positive unit group
    or squre of the unit group depending on the input value of 'tp_units'.

        sage: from extended_hilbert_modgroup.cusp_nf_wrt_lattice_ideal import units_mod_ideal
        sage: K2.<a> = QuadraticField(5)
        sage: I = K2.fractional_ideal(3)
        sage: units_mod_ideal(I)
        [1, -1/2*a + 3/2, -3/2*a + 7/2, -4*a + 9]
        sage: K3.<a> = QuadraticField(3)
        sage: I = K3.fractional_ideal(7)
        sage: units_mod_ideal(I)
        [1, -a + 2, -4*a + 7, -15*a + 26, -56*a + 97, -209*a + 362, -780*a + 1351, -2911*a + 5042]
        sage: units_mod_ideal(I, tp_units = False)
        [1, -4*a + 7, -56*a + 97, -780*a + 1351]

    """
    K = I.number_field()
    Istar = I.idealstar(2)
    if tp_units:
        ulist = totally_positive_unit_group_generators(K)
    else:
        ulist = [K(u**2) for u in K.unit_group().gens_values()]
    elist = [Istar(I.ideallog(u)).order() for u in ulist]
    from sage.misc.mrange import xmrange
    return [K.prod(u ** e for u, e in zip(ulist, ei)) for ei in xmrange(elist)]