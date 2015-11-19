r"""
Kontsevich graph series

"""
from sage.kontsevich_graph_series.kontsevich_graph_sum import KontsevichGraphSum
from sage.structure.element import AlgebraElement
from sage.categories.associative_algebras import AssociativeAlgebras
from sage.rings.ring import Algebra
from sage.structure.parent import Parent
from sage.structure.nonexact import Nonexact
from sage.rings.infinity import infinity

class KontsevichGraphSeries(AlgebraElement):
    def __init__(self, parent, terms, prec=infinity):
        """
        Kontsevich graph series.

        Formal power series with graph sums as coefficients.

        EXAMPLES::

            sage: K = KontsevichGraphSums(QQ)
            sage: star_product_terms = {0 : K([1, KontsevichGraph({'F' : {}, \
            ....:   'G' : {}}, ground_vertices=('F','G'), immutable=True)])}
            sage: S.<h> = KontsevichGraphSeriesRng(K, star_product_terms = \
            ....:   star_product_terms, default_prec = 0)
            sage: S(star_product_terms)
            1*(Kontsevich graph with 0 vertices on 2 ground vertices) + O(h^1)
        """
        AlgebraElement.__init__(self, parent)
        self._terms = terms
        self._prec = prec

    def __hash__(self):
        """
        Return the hash value.
        """
        return hash((self._terms, self._prec))

    def prec(self):
        """
        Precision of the series (possibly infinite).
        """
        return self._prec

    def common_prec(self, other):
        """
        Common precision of the two series (the minimum of the two).
        """
        if self.prec() is infinity:
            return other.prec()
        elif other.prec() is infinity:
            return other.prec()
        return min(self.prec(), other.prec())

    def __getitem__(self, n):
        """
        Coefficient of h^n in the series, where h is the formal variable.
        """
        return self._terms[n] if n in self._terms \
               else self.parent()._base_module(0)

    def __setitem__(self, n, value):
        """
        Assign coefficient of h^n in the series, where h is the formal variable.
        """
        self._terms[n] = value

    def __delitem__(self, n):
        """
        Delete h^n term, where h is the formal variable.
        """
        del self._terms[n]

    def __contains__(self, n):
        """
        Test if coefficient of h^n in the series, where h is the formal
        variable, has been assigned.
        """
        return n in self._terms

    def __len__(self):
        """
        Number of assigned coefficients.
        """
        return len(self._terms)

    def __iter__(self):
        """
        Iterator over the numbers n such that the coefficient of h^n has
        been assigned.
        """
        return iter(self._terms)

    def orders(self):
        """
        Return the iterator from :meth:`.__iter__` as a list.

        Used in :meth:`.reduce` for example.
        """
        return self._terms.keys()

    def degree(self):
        """
        Maximum number n such that the coefficient of h^n has been assigned.
        """
        return max(self)

    def reduce(self):
        """
        Reduce all the coefficients (graph sums).
        """
        for n in self.orders():
            self[n].reduce()
            if self[n] == 0:
                del self[n]

    def __eq__(self, other):
        """
        Test for equality.
        """
        self.reduce()
        other.reduce()
        prec = self.common_prec(other)
        relevant_orders = lambda s: map(lambda k: k <= prec, s)
        if not set(relevant_orders(self)) == set(relevant_orders(other)):
            return False
        for n in relevant_orders(self):
            if self[n] != other[n]:
                return False
        return True

    def __ne__(self, other):
        """
        Test for unequality, using :meth:`.__eq__`.
        """
        return not self.__eq__(other)

    def _repr_(self):
        """
        Representation of the series as a string.
        """
        self.reduce()
        result = ''
        if 0 in self:
            result += str(self[0])
            if len(filter(lambda k: k <= self.prec(), self)) > 1:
                result += ' + '
        result += ' + '.join('(%s)*%s^%d' % \
                             (self[n], self.parent()._generator, n) \
                          for n in self if n > 0 and n <= self.prec())
        if not self._prec is infinity:
            if len(self) > 0:
                result += ' + '
            result += 'O(%s^%d)' % (self.parent()._generator, self.prec() + 1)
        return result

    def _add_(self, other):
        """
        Add two series.
        """
        prec = self.common_prec(other)
        relevant_orders = lambda s: filter(lambda k: k <= prec, s)
        sum_keys = set(relevant_orders(self)) | set(relevant_orders(other))
        sum_terms = {n: self[n] + other[n] for n in sum_keys}
        return self.parent()(sum_terms, prec=prec)

    def _rmul_(self, other):
        """
        Scalar multiplication.
        """
        if other in self.parent().base_ring():
            return self.parent()({n : other*self[n] for n in self},
                                 prec=self.prec())

    def _mul_(self, other):
        """
        Star product.
        """
        prec = self.common_prec(other)
        N = self.parent().default_prec()
        product_terms = {}
        for n in range(0, min(N, prec) + 1):
            product_terms[n] = 0
            for k in range(0, n + 1):
                for a in range(0, n - k + 1):
                    b = n - k - a
                    product_terms[n] += \
                            self.parent()._star_product_series[k].subs( \
                            self[a], other[b])
        return self.parent()(product_terms, prec=prec)

class KontsevichGraphSeriesRng(Algebra, Nonexact):
    Element = KontsevichGraphSeries

    def __init__(self, base_module, names=None, name=None,
                 star_product_terms={}, default_prec=2):
        """
        Kontsevich graph series rng (ring without identity).

        EXAMPLES::
            sage: K = KontsevichGraphSums(QQ)
            sage: star_product_terms = {0 : K([1, KontsevichGraph({'F' : {}, \
            ....:   'G' : {}}, ground_vertices=('F','G'), immutable=True)])}
            sage: S.<h> = KontsevichGraphSeriesRng(K, star_product_terms = \
            ....:   star_product_terms, default_prec = 0)
        """
        Parent.__init__(self, base_module.base_ring(),
                        category=AssociativeAlgebras(base_module.base_ring()))
        Nonexact.__init__(self, default_prec)
        self._base_module = base_module
        if name:
            self._generator = name
        elif names:
            self._generator = names[0]
        else:
            raise ValueError('Must provide a name for the generator')
        self._star_product_series = {}
        self._star_product_series = self.element_class(self, star_product_terms,
                                               prec=default_prec)

    def _repr_(self):
        """
        Representation of the rng as a string.
        """
        return "Kontsevich graph series rng in %s over %s" % (self._generator,
                self._base_module) + \
               ", with star product %s" % self._star_product_series

    def _element_constructor_(self, terms, prec=None):
        """
        Make a KontsevichGraphSeries in ``self`` from ``terms``.
        """
        if prec is None:
            prec = self.default_prec()
        if isinstance(terms, KontsevichGraphSeries):
            terms = terms._terms
            prec = terms._prec
        return self.element_class(self, terms, prec=prec)

    # The following three methods make the generator notation
    # S.<h> = KontsevichGraphSeriesRng(...) work.

    def ngens(self):
        """
        The number of generators (that is, 1).
        """
        return 1

    def gen(self, i=0):
        """
        The ith generator.
        """
        if i != 0:
            raise ValueError('There is only one generator')
        return self._generator

    def gens(self):
        """
        The generators.
        """
        return (self._generator,)
