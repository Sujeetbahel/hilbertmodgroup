from sage.structure.element import Element
from sage.structure.richcmp import richcmp, rich_to_bool
from sage.modular.cusps_nf import NFCusps, NFCusp
from sage.modular.cusps_nf import list_of_representatives, units_mod_ideal


def gens_reduced_wrt_base_ideal(base_ideal, ideal):
    """
        Return the two generators (a, b) of the ideal in the sense, ideal= a*OK + b*(base_ideal.inverse())

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import gens_reduced_wrt_base_ideal
            sage: x = polygen(ZZ, 'x')
            sage: K.<a> = NumberField(x^2 - 5)
            sage: base_ideal=K.different()
            sage: ideal = K.fractional_ideal(3)
            sage: gens_reduced_wrt_base_ideal(base_ideal, ideal)
            (3, 0)
            sage: K1 = NumberField(x**4 - 17*x**2 + 36,names='a')
            sage: a=K1.gen()
            sage: base_ideal = K1.different()
            sage: ideal = K1.fractional_ideal(2, a)
            sage: gens_reduced_wrt_base_ideal(base_ideal, ideal)
            (2, 7/6*a^3 + 6*a^2 + 13/6*a - 51)
    """
    if not (base_ideal.number_field() == ideal.number_field()):
        return "base_ideal and ideal should be from the same ring of integers of a field"
    else:
        K = base_ideal.number_field()
        OK = K.OK()
        if base_ideal == OK.fractional_ideal(1):
            if ideal.is_principal():
                return tuple((ideal.gens_reduced()[0], 0))
            else:
                return ideal.gens_reduced()
        elif ideal.is_principal():
            a = ideal.gens_reduced()[0]
            return tuple((a, 0))
        else:
            a = ideal.gens_reduced()[0]
            temp = base_ideal * ideal
            if temp.is_principal():
                b = temp.gens_reduced()[0]
                return tuple((a, b))
            else:
                possible = list_of_representatives(ideal)
                for inverse in possible:
                    if (temp * inverse).is_principal():
                        b = temp * inverse
                return tuple((a, b.gens_reduced()[0]))


def ideal_wrt_base_ideal(base_ideal, x: tuple):
    """
        Return the ideal  in the sense, ideal = a*OK + b*(base_ideal.inverse())

        EXAMPLES::
            sage: sage: from extended_hilbert_modgroup.all import ideal_wrt_base_ideal
            sage: x = polygen(ZZ, 'x')
            sage: K.<a> = NumberField(x^2 - 5)
            sage: base_ideal=K.different()
            sage: ideal = K.fractional_ideal(3)
            sage: gens_reduced_wrt_base_ideal(base_ideal, ideal)
            (3, 0)
            sage: ideal_wrt_base_ideal(base_ideal, gens_reduced_wrt_base_ideal(base_ideal, ideal)) == ideal
            True

            sage: K1 = NumberField(x**4 - 17*x**2 + 36,names='a')
            sage: a=K1.gen()
            sage: base_ideal = K1.different()
            sage: ideal = K1.fractional_ideal(2, a)
            sage: gens_reduced_wrt_base_ideal(base_ideal, ideal)
            (2, 7/6*a^3 + 6*a^2 + 13/6*a - 51)
            sage: ideal_wrt_base_ideal(base_ideal, gens_reduced_wrt_base_ideal(base_ideal, ideal)) == ideal
            True
    """
    K = base_ideal.number_field()
    if x[1] == 0:
        return K.OK().fractional_ideal(x[0])
    else:
        return x[0] * K.OK().fractional_ideal(1) + x[1] * (base_ideal.inverse())


class NFCusp_wrt_base_ideal(Element):
    r"""
    Create a number field cusp, i.e., an element of `\mathbb{P}^1(k)` with respect to a base ideal.
    In the standard cusp  for a field the base ideal is OK. Ideally they are same but the ideal
    represented by them differs. Moreover, the ABmatrix for the cusp will be different.
    parent- NFCusps.
    INPUT:

    - ``base_ideal`` -- the ideal of a number field over which the cusp is defined.

    - ``a`` -- it can be a number field element (integral or not), or
      a number field cusp.

    - ``b`` -- (optional) when present, it must be either Infinity or
      coercible to an element of the number field.

    - ``lreps`` -- (optional) a list of chosen representatives for all the
      ideal classes of the field. When given, the representative of the cusp
      will be changed so its associated ideal is one of the ideals in the list.

    OUTPUT:

    ``[a: b]`` -- a number field cusp with respect to the base ideal I.

    EXAMPLES::
        sage: from extended_hilbert_modgroup.all import NFCusp_wrt_base_ideal
        sage: x = polygen(ZZ, 'x')
        sage: K.<a> = NumberField(x^2 - 5)
        sage: OK=K.OK()
        sage: base_ideal=K.different()
        sage: NFCusp_wrt_base_ideal(base_ideal, a, 2)
        Cusp [a: 2] of Number Field in a with defining polynomial x^2 - 5 with respect to the base ideal Fractional ideal (-a)
        sage: NFCusp_wrt_base_ideal(base_ideal, (a,2))
        Cusp [a: 2] of Number Field in a with defining polynomial x^2 - 5 with respect to the base ideal Fractional ideal (-a)
        sage: NFCusp_wrt_base_ideal(k, a, 2/(a+1))
        Cusp [a: 1/2*a - 1/2] of Number Field in a with defining polynomial x^2 - 5 with respect to the base ideal Fractional ideal (-a)

    Cusp Infinity:

    ::  sage: from extended_hilbert_modgroup.all import NFCusp_wrt_base_ideal
        sage: NFCusp_wrt_base_ideal(base_ideal, 0)
        Cusp [0: 1] of Number Field in a with defining polynomial x^2 - 5 with respect to the base ideal Fractional ideal (-a)
        sage: NFCusp_wrt_base_ideal(base_ideal, oo)
        Cusp Infinity of Number Field in a with defining polynomial x^2 - 5 with respect to the base ideal Fractional ideal (-a)
        sage: NFCusp_wrt_base_ideal(base_ideal, 3*a, oo)
        Cusp [0: 1] of Number Field in a with defining polynomial x^2 - 5 with respect to the base ideal Fractional ideal (-a)
        sage: NFCusp_wrt_base_ideal(base_ideal, a + 5, 0)
        Cusp Infinity of Number Field in a with defining polynomial x^2 - 5 with respect to the base ideal Fractional ideal (-a)
    """

    def __init__(self, base_ideal, a, b=None, parent=None, lreps=None):
        self._base_ideal = base_ideal
        self._OK = base_ideal.number_field().OK()
        self._number_field = base_ideal.number_field()
        if parent is None:
            parent = NFCusps(self._number_field)
        Element.__init__(self, parent)
        K = self._number_field
        R = self._OK
        if isinstance(a, NFCusp_wrt_base_ideal):
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
            cusp = NFCusp_wrt_base_ideal(base_ideal, a, b)
            self.__a = cusp.numerator()
            self.__b = cusp.denominator()

    def _repr_(self):
        """
        String representation of this cusp.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_base_ideal
            sage: x = polygen(ZZ, 'x')
            sage: K.<a> = NumberField(x^2 - 3)
            sage: base_ideal =K.different()
            sage: c = NFCusp_wrt_base_ideal(base_ideal, a, 2);c
            Cusp [a: 2] of Number Field in a with defining polynomial x^2 - 3 with respect to the base ideal Fractional ideal (-2*a)
            sage: c._repr_()
            'Cusp [a: 2] of Number Field in a with defining polynomial x^2 - 3 with respect to the base ideal Fractional ideal (-2*a)'
        """
        if self.__b.is_zero():
            return "Cusp Infinity of %s with respect to the base ideal %s" % (
                self.parent().number_field(), self.base_ideal())
        else:
            return "Cusp [%s: %s] of %s with respect to the base ideal %s" % (self.__a, self.__b,
                                                                              self.parent().number_field(),
                                                                              self.base_ideal())

    def base_ideal(self):
        """
        Return the base ideal associated to the cusp.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_base_ideal
            sage: x = polygen(ZZ, 'x')
            sage: K.<a> = NumberField(x^2 - 3)
            sage: base_ideal =K.different()
            sage: c = NFCusp_wrt_base_ideal(base_ideal, a, 2);c
            Cusp [a: 2] of Number Field in a with defining polynomial x^2 - 3 with respect to the base ideal Fractional ideal (-2*a)
            sage: c.base_ideal()
            Fractional ideal (-2*a)
        """
        return self._base_ideal

    def OK(self):
        """
        Return the ring of integers of the number field associated to the cusp.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_base_ideal
            sage: x = polygen(ZZ, 'x')
            sage: K.<a> = NumberField(x^2 - 3)
            sage: base_ideal =K.different()
            sage: c = NFCusp_wrt_base_ideal(base_ideal, a, 2);c
            Cusp [a: 2] of Number Field in a with defining polynomial x^2 - 3 with respect to the base ideal Fractional ideal (-2*a)
            sage: c.OK()
            Maximal Order generated by a in Number Field in a with defining polynomial x^2 - 3
        """
        return self._OK

    def number_field(self):
        """
        Return the number field associated to the cusp.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_base_ideal
            sage: x = polygen(ZZ, 'x')
            sage: K.<a> = NumberField(x^2 - 3)
            sage: base_ideal =K.different()
            sage: c = NFCusp_wrt_base_ideal(base_ideal, a, 2);c
            Cusp [a: 2] of Number Field in a with defining polynomial x^2 - 3 with respect to the base ideal Fractional ideal (-2*a)
            sage: c.number_field()
            Number Field in a with defining polynomial x^2 - 3
        """
        return self.parent().number_field()

    def is_infinity(self):
        """
        Return ``True`` if this is the cusp infinity.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_base_ideal
            sage: x = polygen(ZZ, 'x')
            sage: K.<a> = NumberField(x^2 - 3)
            sage: base_ideal = K.OK().fractional_ideal(2)
            sage: NFCusp_wrt_base_ideal(base_ideal, a, 2).is_infinity()
            False
            sage: NFCusp_wrt_base_ideal(base_ideal, 2, 0).is_infinity()
            True
            sage: NFCusp_wrt_base_ideal(base_ideal, oo).is_infinity()
            True
        """
        return self.__b == 0

    def numerator(self):
        """
        Return the numerator of the cusp ``self``.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_base_ideal
            sage: x = polygen(ZZ, 'x')
            sage: K.<a> = NumberField(x^2 -5)
            sage: base_ideal = K.OK().fractional_ideal(2)
            sage: c = NFCusp_wrt_base_ideal(base_ideal, a, 2)
            sage: c.numerator()
            a
            sage: d = NFCusp_wrt_base_ideal(base_ideal, 1, a)
            sage: d.numerator()
            1
            sage: NFCusp_wrt_base_ideal(base_ideal, oo).numerator()
            1
        """
        return self.__a

    def denominator(self):
        """
        Return the numerator of the cusp ``self``.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_base_ideal
            sage: x = polygen(ZZ, 'x')
            sage: K.<a> = NumberField(x^2 -5)
            sage: base_ideal = K.OK().fractional_ideal(2)
            sage: c = NFCusp_wrt_base_ideal(base_ideal, a, 2)
            sage: c.denominator()
            2
            sage: d = NFCusp_wrt_base_ideal(base_ideal, 1, a)
            sage: d.denominator()
            a
            sage: NFCusp_wrt_base_ideal(base_ideal, oo).denominator()
            0
        """
        return self.__b

    def _number_field_element_(self):
        """
        Coerce to an element of the number field.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_base_ideal
            sage: x = polygen(ZZ, 'x')
            sage: K.<a> = NumberField(x^2 - 5)
            sage: base_ideal = K.OK().fractional_ideal(2)
            sage: NFCusp_wrt_base_ideal(base_ideal, a, 2)._number_field_element_()
            1/2*a
            sage: NFCusp_wrt_base_ideal(base_ideal, 1, a + 1)._number_field_element_()
            1/4*a - 1/4
        """
        if self.__b.is_zero():
            raise TypeError("%s is not an element of %s" % (self, self.number_field()))
        K = self.number_field()
        return K(self.__a / self.__b)

    def _ring_of_integers_element_(self):
        """
        Coerce to an element of the ring of integers of the number field.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_base_ideal
            sage: x = polygen(ZZ, 'x')
            sage: K.<a> = NumberField(x^2 -3)
            sage: base_ideal = K.OK().fractional_ideal(2)
            sage: NFCusp_wrt_base_ideal(base_ideal, a+1)._ring_of_integers_element_()
            a + 1
            sage: NFCusp_wrt_base_ideal(base_ideal, 1, a + 1)._ring_of_integers_element_()
            Traceback (most recent call last):
            ...
            TypeError: Cusp [1: a + 1] of Number Field in a with defining polynomial x^2 - 3 with respect to the base ideal
            Fractional ideal (2) is not an integral element
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
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_base_ideal
            sage: x = polygen(ZZ, 'x')
            sage: K.<a> = NumberField(x^2 - 11)
            sage: base_ideal = K.different()
            sage: latex(NFCusp_wrt_base_ideal(base_ideal, 3*a, a + 1)) # indirect doctest
            \[3 a: a + 1\]
            sage: latex(NFCusp_wrt_base_ideal(base_ideal, oo))
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
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_base_ideal
            sage: x = polygen(ZZ, 'x')
            sage: K.<a> = NumberField(x^2-5)
            sage: base_ideal = K.OK().fractional_ideal(2)

        Comparing with infinity::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_base_ideal
            sage: c = NFCusp_wrt_base_ideal(base_ideal, a,2)
            sage: d = NFCusp_wrt_base_ideal(base_ideal, oo)
            sage: c < d
            True
            sage: NFCusp_wrt_base_ideal(base_ideal, oo) < d
            False

        Comparison as elements of the number field::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_base_ideal
            sage: NFCusp_wrt_base_ideal(base_ideal, 2/3) < NFCusp_wrt_base_ideal(base_ideal, 5/2)
            True
            sage: K(2/3) < K(5/2)
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
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_base_ideal
            sage: x = polygen(ZZ, 'x')
            sage: K.<a> = NumberField(x^2 - 11)
            sage: base_ideal = K.OK().fractional_ideal(2)
            sage: c = NFCusp_wrt_base_ideal(base_ideal, a, a+1); c
            Cusp [a: a + 1] of Number Field in a with defining polynomial x^2 - 11 with respect to the base ideal Fractional ideal (2)
            sage: -c
            Cusp [-a: a + 1] of Number Field in a with defining polynomial x^2 - 11 with respect to the base ideal Fractional ideal (2)
        """
        return NFCusp_wrt_base_ideal(self.base_ideal(), -self.__a, self.__b)

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
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_base_ideal
            sage: x = polygen(ZZ, 'x')
            sage: K.<a> = NumberField(x^2 - 23)
            sage: base_ideal = K.OK().fractional_ideal(2)
            sage: beta = NFCusp_wrt_base_ideal(base_ideal, 0, 1)
            sage: beta.apply([0, -1, 1, 0])
            Cusp Infinity of Number Field in a with defining polynomial x^2 - 23 with respect to the base ideal Fractional ideal (2)
            sage: beta.apply([1, a, 0, 1])
            Cusp [a: 1] of Number Field in a with defining polynomial x^2 - 23 with respect to the base ideal Fractional ideal (2)
        """
        return NFCusp_wrt_base_ideal(self.base_ideal(), g[0] * self.__a + g[1] * self.__b,
                                     g[2] * self.__a + g[3] * self.__b)

    def ideal(self):
        """
        Return the ideal associated to the cusp ``self``.

        EXAMPLES::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_base_ideal
            sage: x = polygen(ZZ, 'x')
            sage: K.<a> = NumberField(x^2 -7)
            sage: base_ideal = K.OK().fractional_ideal(2)
            sage: alpha = NFCusp(K, 3, a-1)
            sage: alpha.ideal()
            Fractional ideal (a + 2)
            sage: beta = NFCusp_wrt_base_ideal(base_ideal, 3, a-1)
            Fractional ideal (1/2*a - 1/2)
        """
        return ideal_wrt_base_ideal(self.base_ideal(), (self.__a, self.__b))

    def ABmatrix_wrt_base_ideal(self, return_B=False):
        """
        Return AB-matrix associated to the cusp ``self``.

        EXAMPLES:

        ::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_base_ideal
            sage: x = polygen(ZZ, 'x')
            sage: K.<a> = NumberField(x^2 - 11)
            sage: base_ideal = K.OK().fractional_ideal(2)
            sage: alpha = NFCusp_wrt_base_ideal(base_ideal, oo)
            sage: alpha.ABmatrix_wrt_base_ideal()
            [1, 0, 0, 1]

        ::

            sage: alpha = NFCusp_wrt_base_ideal(base_ideal, 0)
            sage: alpha.ABmatrix_wrt_base_ideal()
            [0, -1, 1, 0]

        Note that the AB-matrix associated to a cusp is not unique, and the
        output of the ``ABmatrix`` function may change.

        ::

            sage: alpha = NFCusp_wrt_base_ideal(base_ideal, 3/2, a-1)
            sage: M = alpha.ABmatrix_wrt_base_ideal()
            sage: M
            [3*a + 3, -1/2*a - 1/2, 20, -3]
            sage: M[0] == alpha.numerator() and M[2] == alpha.denominator()
            True

        An AB-matrix associated to a cusp alpha will send Infinity to alpha:

        ::

            sage: alpha = NFCusp_wrt_base_ideal(base_ideal, 3, a-1)
            sage: M = alpha.ABmatrix_wrt_base_ideal()
            sage: M[0] == alpha.numerator() and M[2] == alpha.denominator()
            True
            sage: OK = K.fractional_ideal(1)
            sage: ((M[1]*base_ideal+M[3]*OK)*alpha.ideal()).is_principal()
            True
            sage: NFCusp_wrt_base_ideal(base_ideal, oo).apply(M) == alpha
            True
        """
        K = self.number_field()
        A = self.ideal()
        if A.is_principal():
            B = K.fractional_ideal(1)
        else:
            B = K.fractional_ideal(A.gens_reduced()[1]) / A
        assert (A * B).is_principal()
        a1 = self.__a
        a2 = self.__b
        g = (A * B).gens_reduced()[0]
        if self.is_infinity():
            B = K.OK().fractional_ideal(1)
            if return_B:
                return [1, 0, 0, 1], B
            else:
                return [1, 0, 0, 1]
        if not self:
            # gens = gens_reduced_wrt_base_ideal(self.base_ideal(), self.base_ideal().inverse()*B)
            if return_B:
                return [self.__a, -1 / self.__b, self.__b, 0], B
            else:
                return [self.__a, -1 / self.__b, self.__b, 0]
        Ainv = A ** (-1)
        A1 = a1 * Ainv
        A2 = a2 * (self.base_ideal().inverse()) * Ainv
        r = A1.element_1_mod(A2)
        b1 = -(1 - r) / a2 * g
        b2 = (r / a1) * g
        ABM = [a1, b1, a2, b2]
        if return_B:
            return ABM, B
        else:
            return ABM

    def is_Gamma0_wrt_base_ideal_equivalent(self, other, N, Transformation=False):
        r"""
        Check if cusps ``self`` and ``other`` are `\Gamma_0(N)_wrt base_ideal`- equivalent.

        INPUT:

        - ``other`` -- a number field cusp wrt base_ideal or a list of two number field
          elements which define a cusp wrt base_ideal.

        - ``N`` -- an ideal of the number field (level)

        OUTPUT:

        - bool -- ``True`` if the cusps are equivalent.

        - a transformation matrix -- (if ``Transformation=True``) a list of
          integral elements [a, b, c, d] which are the entries of a 2x2 matrix
          M in `\Gamma_0(N) wrt base_ideal` such that M * ``self`` = ``other`` if ``other``
          and ``self`` are `\Gamma_0(N)`- equivalent. If ``self`` and ``other``
          are not equivalent it returns zero.

        EXAMPLES:

        ::
            sage: from exteded_hilbert_modgroup.all import NFCusp_wrt_base_ideal
            sage: x = polygen(ZZ, 'x')
            sage: K.<a> = NumberField(x^2 - 3)
            sage: N = K.fractional_ideal(1)
            sage: base_ideal = K.different()
            sage: alpha = NFCusp_wrt_base_ideal(base_ideal, 0)
            sage: beta = NFCusp_wrt_base_ideal(base_ideal, oo)
            sage: alpha.is_Gamma0_wrt_base_ideal_equivalent(beta, N)
            True
            sage: b, M = alpha.is_Gamma0_wrt_base_ideal_equivalent(beta, K.fractional_ideal(1),Transformation=True)
            sage: alpha.apply(M)
            Cusp Infinity of Number Field in a with defining polynomial x^2 - 3 with respect to the base ideal Fractional ideal (-2*a)
            sage: M[2] in base_ideal
            True
            sage: M[1] in base_ideal.inverse()
            True
            sage: from sage.matrix.constructor import Matrix
            sage: M = Matrix(K, 2, M)
            sage: det(M)
            1

        ::
            sage: from extended_hilbert_modgroup.all import NFCusp_wrt_base_ideal
            sage: K.<a> = NumberField(x^2 - 5)
            sage: N = K.fractional_ideal(1)
            sage: base_ideal = K.different()
            sage: alpha1 = NFCusp_wrt_base_ideal(base_ideal, a+1, 4)
            sage: alpha2 = NFCusp_wrt_base_ideal(base_ideal, a-8, 29)
            sage: alpha1.is_Gamma0_wrt_base_ideal_equivalent(alpha2, N)
            True
            sage: b, M = alpha1.is_Gamma0_wrt_base_ideal_equivalent(alpha2, N, Transformation=True)
            sage: alpha1.apply(M) == alpha2
            True
            sage: M[2] in base_ideal
            True
            sage: M[1] in base_ideal.inverse()
            True
            sage: from sage.matrix.constructor import Matrix
            sage: M = Matrix(K, 2, M)
            sage: det(M)
            1
        """
        K = self.number_field()
        other = NFCusp_wrt_base_ideal(self.base_ideal(), other)
        if not (self.ideal() / other.ideal()).is_principal():
            if not Transformation:
                return False
            else:
                return False
        reps = list_of_representatives(N * self.base_ideal())
        alpha1 = NFCusp_wrt_base_ideal(self.base_ideal(), self, lreps=reps)
        # print(alpha1.ideal())
        alpha2 = NFCusp_wrt_base_ideal(self.base_ideal(), other, lreps=reps)
        # print(alpha2.ideal())
        delta = K.ideal(alpha1.__b) + N
        if (K.ideal(alpha2.__b) + N) != delta:
            if not Transformation:
                return False
            else:
                return False, 0

        M1, B1 = alpha1.ABmatrix_wrt_base_ideal(True)
        # print(M1)
        M2, B2 = alpha2.ABmatrix_wrt_base_ideal(True)
        A = alpha1.ideal()
        # print('A=', A)
        # OK = self.number_field().OK().fractional_ideal(1)
        # if not M1[1]:
        #    B = M1[3]*OK
        # elif not M1[3]:
        #    B = M1[1] * self.base_ideal()
        # else:
        #    B = M1[1] * self.base_ideal() + M1[3] * OK
        # B = OK
        # print('B=', B)
        if B1 == B2:
            B = B1
        else:
            return 'B1 and B2 should be same'
        ABdelta = A * B * delta * delta * self.base_ideal()

        units = units_mod_ideal(ABdelta)
        for u in units:
            if (M2[2] * M1[3] - u * M1[2] * M2[3]) in ABdelta:
                if not Transformation:
                    return True
                else:
                    AuxCoeff = [1, 0, 0, 1]
                    Aux = M2[2] * M1[3] - u * M1[2] * M2[3]
                    if Aux in A * B * N * self.base_ideal():
                        if u != 1:
                            AuxCoeff[3] = u
                    else:
                        A1 = (A * B * N * self.base_ideal()) / ABdelta
                        A2 = B * K.fractional_ideal(M1[2] * M2[2]) / (A * self.base_ideal() * ABdelta)
                        f = A1.element_1_mod(A2)
                        w = ((1 - f) * Aux) / (M1[2] * M2[2])
                        print('w=', w)
                        AuxCoeff[3] = u
                        print('u=', u)
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