r"""
Kontsevich graph sums

"""
from sage.kontsevich_graph_series.kontsevich_graph import KontsevichGraph
from sage.structure.element import ModuleElement
from sage.modules.module import Module
from sage.symbolic.ring import is_SymbolicExpressionRing

class KontsevichGraphSum(ModuleElement):
    def __init__(self, parent, terms):
        """
        Kontsevich graph sum.

        INPUT:

        - ``parent`` -- a ``KontsevichGraphSums`` module.
        - ``terms`` -- list of ``(coefficient, graph)`` tuples,
          where ``coefficient`` is in ``parent.base_ring()``,
          and ``graph`` is an immutable KontsevichGraph.

        OUTPUT:

        A formal sum of Kontsevich graphs.

        EXAMPLES::

            sage: K = KontsevichGraphSums(QQ)
            sage: KG = KontsevichGraph(ground_vertices=(), immutable=True)
            sage: KontsevichGraphSum(K, [(1/2, KG)])
            1/2*(Kontsevich graph with 0 vertices on 0 ground vertices)
        """
        if terms == 0:
            terms = []
        if not isinstance(terms, list):
            raise TypeError('Input must be a list of terms.')
        if not all(isinstance(t, tuple) and len(t) == 2 for t in terms):
            raise TypeError('Terms must be (coefficient, graph) tuples.')
        if not all(c in parent.base_ring() and isinstance(g, KontsevichGraph)
                   and getattr(g, '_immutable', False) for (c,g) in terms):
            raise TypeError('Coefficients must be in base ring, and ' +
                            'graphs must be immutable KontsevichGraphs.')
        self._terms = terms
        ModuleElement.__init__(self, parent=parent)
    def _rmul_(self, c):
        """
        Return the product of ``c`` and ``self``.

        INPUT:

        - ``c`` -- multiplicand.

        OUTPUT:

        Kontsevich graph sum with coefficients ``c`` times those of ``self``.

        EXAMPLES::

            sage: K = KontsevichGraphSums(QQ)
            sage: KG = KontsevichGraph(ground_vertices=(), immutable=True)
            sage: 2*KontsevichGraphSum(K, [(1/2, KG)])
            1*(Kontsevich graph with 0 vertices on 0 ground vertices)
        """
        return self.parent()([(c*d,g) for (d,g) in self._terms])
    def _add_(self, other):
        """
        Return the sum of ``self`` and ``other``.

        INPUT:

        - ``other`` -- a KontsevichGraphSum.

        OUTPUT:

        The sum of ``self`` and ``other``.

        EXAMPLES::

            sage: K = KontsevichGraphSums(QQ)
            sage: KG = KontsevichGraph(ground_vertices=(), immutable=True)
            sage: KontsevichGraphSum(K, [(1/2, KG)]) + \
                  KontsevichGraphSum(K, [(1/2, KG)])
            1*(Kontsevich graph with 0 vertices on 0 ground vertices)
        """
        return self.parent()(self._terms + other._terms)
    def __eq__(self, other):
        """
        Compare ``self`` and ``other`` for equality.

        Currently tests for equality of coefficients of identical graphs.

        INPUT:

        - ``other`` -- a KontsevichGraphSum with the same parent.

        EXAMPLES::

            sage: K = KontsevichGraphSums(QQ)
            sage: KG = KontsevichGraph(ground_vertices=(), immutable=True)
            sage: A = KontsevichGraphSum(K, [(1/2, KG)]) + \
                  KontsevichGraphSum(K, [(1/2, KG)])
            sage: B = KontsevichGraphSum(K, [(1, KG)])
            sage: A == B
            True
        """
        self.reduce()
        other.reduce()
        return set(self._terms) == set(other._terms)
    def __hash__(self):
        """
        Return the hash value.
        """
        return hash(tuple(self._terms))
    def reduce(self):
        """
        Reduce the sum by collecting terms with the same graph.
        """
        graphs = set(g for (c,g) in self._terms)
        coefficient = lambda g: sum(c for (c,h) in self._terms if h == g)
        self._terms = [(coefficient(g), g) for g in graphs
                        if coefficient(g) != self.base_ring()(0)]
    def _repr_(self):
        """
        EXAMPLES::

            sage: K = KontsevichGraphSums(QQ)
            sage: KG = KontsevichGraph(ground_vertices=(), immutable=True)
            sage: KontsevichGraphSum(K, [(1/2, KG)])
            1/2*(Kontsevich graph with 0 vertices on 0 ground vertices)
        """
        self.reduce()
        if self._terms == []:
            return '0'
        parenthesize = lambda c: str(c)
        if is_SymbolicExpressionRing(self.base_ring()):
            from sage.symbolic.operators import add_vararg
            is_sum = lambda x: self.base_ring()(x).operator() == add_vararg
            parenthesize = lambda c: '(%s)' % c if is_sum(c) else c
        return ' + '.join('%s*(%s)' % (parenthesize(c), g)
                          for (c,g) in self._terms)

class KontsevichGraphSums(Module):
    """
    The module of Kontsevich graph sums with coefficients in some ring.
    """
    Element = KontsevichGraphSum
    def _repr_(self):
        """
        EXAMPLES::

            sage: KontsevichGraphSums(QQ)
            Module of Kontsevich graph sums over Rational Field
            sage: KontsevichGraphSums(SR)
            Module of Kontsevich graph sums over Symbolic Ring
        """
        return 'Module of Kontsevich graph sums over %s' % self.base_ring()
    def _element_constructor_(self, terms):
        """
        Make a KontsevichGraphSum in ``self`` from ``terms``.

        INPUT:

        - ``terms`` -- KontsevichGraphSum, list of terms, or 0.
        """
        if isinstance(terms, KontsevichGraphSum): terms = terms._terms
        return self.element_class(self, terms)
    def __cmp__(self, other):
        """
        Compare ``self`` and ``other`` for equality.
        """
        if not isinstance(other, KontsevichGraphSums):
            return cmp(type(other), KontsevichGraphSums)
        return cmp(self.base_ring(), other.base_ring())
    def _an_element_(self):
        """
        EXAMPLES::

            sage: KontsevichGraphSums(QQ).an_element()
            1/2*(Kontsevich graph with 1 vertices on 2 ground vertices)
            sage: KontsevichGraphSums(SR).an_element()
            some_variable*(Kontsevich graph with 1 vertices on 2
            ground vertices)

        """
        KG = KontsevichGraph({'F' : {}, 'G' : {}, 1 : {'F', 'G'}},
                             ground_vertices=('F', 'G'),
                             immutable=True)
        return self.element_class(self, [(self.base_ring().an_element(), KG)])
