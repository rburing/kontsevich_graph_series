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

        A formal sum of Kontsevich graphs, modulo the relation that
        swapping two edges (L and R) originating from an internal vertex
        introduces a minus sign.

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

        Checks if the reduced difference is zero.

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
        difference = self - other
        difference.reduce()
        return difference._terms == []

    def __ne__(self, other):
        """
        Unequality testing by using :meth:`.__eq__`.
        """
        return not self.__eq__(other)

    def __hash__(self):
        """
        Return the hash value.
        """
        return hash(tuple(self._terms))

    def reduce(self):
        """
        Reduce the sum by collecting terms with proportional graphs.

        Swapping the edge labels (L and R) of two edges originating from an
        internal vertex introduces a minus sign. Hence graphs that differ only
        in their edge labelings are related by a sign, equal to
        (-1)^(the number of edge swaps).

        ALGORITHM:

        First collect terms with exactly the same graph. Call this the list
        of old terms. For the first old term, find all the signed edge
        relabelings of the graph in the old terms, and add up the signed
        coefficients (+ or - according to the number of edge swaps).
        If the result is nonzero, this gives a new term. In any case, remove
        all the old terms involving these relabelings. Rinse, repeat.
        """
        # Collect terms with exactly the same graph.
        all_graphs = [g for (c,g) in self._terms]
        graphs = list(set(all_graphs))
        graphs.sort(key=all_graphs.index) # preserve ordering of terms
        coefficient = lambda g: sum(c for (c,h) in self._terms if h == g)
        self._terms = [(coefficient(g), g) for g in graphs
                        if coefficient(g) != self.base_ring()(0)]

        # Remove terms with graphs which are zero.
        self._terms = filter(lambda (c,g): not g.is_zero(), self._terms)
        # This is necessary for the next step, where we assume that all
        # edge relabelings are distinct.

        # Collect terms with the same graph up to sign.
        old_terms = list(self._terms)
        self._terms = []
        while len(old_terms) > 0:
            _, g = old_terms[0]
            graphs = [h for (d,h) in old_terms]
            signed_relabelings = filter(lambda (h, s): h in graphs, \
                                        g.edge_relabelings(signs=True))
            coefficient = lambda g: sum([d for (d,h) in old_terms \
                                         if h == g])
            total = sum(s*coefficient(h) for (h,s) in signed_relabelings)
            if total != self.base_ring()(0):
                self._terms.append((total, g))
            for (h,s) in signed_relabelings:
                old_terms.remove((coefficient(h), h))

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

    def subs(self, *args):
        """
        Substitute the KontsevichGraphSums ``args`` in place of the ground
        vertices, by multilinearity and the (iterated) Leibniz rule.

        Here, the Leibniz rule means summing over all possible attachments.
        """
        assert all(s in self.parent() for s in args)
        assert all(len(g.ground_vertices()) == len(args) \
                   for (c,g) in self._terms)
        total_terms = []
        for (c,g) in self._terms:
            from itertools import product
            for terms in product(*[s._terms for s in args]):
                coeffs, graphs = zip(*terms)
                import operator
                coeff = c*reduce(operator.mul, coeffs)
                # Attach in all the possible ways.
                def possible_attachments(n):
                    deg = g.in_degree(g.ground_vertices()[n])
                    if deg == 0:
                        yield {}
                    else:
                        srcs = g.neighbors_in(g.ground_vertices()[n])
                        for dsts in product(graphs[n].vertices(), repeat=deg):
                            yield dict(zip(srcs, dsts))
                for attachments in product(*[possible_attachments(n) \
                                             for n in range(0, len(args))]):
                    graph_attachments = zip(graphs, attachments)
                    total_terms.append((coeff, g.attach(*graph_attachments)))
        return self.parent()(total_terms)


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
        KG = KontsevichGraph({'F' : {}, 'G' : {}, 1 : {'F' : 'L', 'G' : 'R'}},
                             ground_vertices=('F', 'G'),
                             immutable=True)
        return self.element_class(self, [(self.base_ring().an_element(), KG)])
