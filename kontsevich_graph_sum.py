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

    def __iter__(self):
        """
        Iterator over the (coefficient, graph) terms in the sum.
        """
        return iter(self._terms)

    def __len__(self):
        """
        Number of terms in the sum.
        """
        return len(self._terms)

    def coefficient(self, g):
        """
        The coefficient of the graph ``g`` in the sum, also counting
        signed relabelings.
        """
        graphs = [h for (d,h) in self._terms]
        signed_relabelings = filter(lambda (h, s): h in graphs, \
                                    g.edge_relabelings(signs=True))
        coefficient = lambda g: sum([d for (d,h) in self._terms \
                                     if h == g])
        total = sum(s*coefficient(h) for (h,s) in signed_relabelings)
        return total

    def coefficients(self, gs):
        """
        The coefficients of the graphs ``gs`` in the sum, also counting
        signed relabelings.
        """
        return [self.coefficient(g) for g in gs]

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

    def __mul__(self, other):
        """
        Pointwise product.

        For technical reasons, ground vertices should be distinct.
        """
        prod_terms = []
        for (c,g) in self._terms:
            for (d,h) in other._terms:
                prod_terms.append((c*d, g.union(h, same_ground=False)))
        return self.parent()(prod_terms)

    def hochschild_differential(self):
        """
        The Hochschild differential.
        """
        diff = self.parent()(0)
        for (c,g) in self._terms:
            k = len(g.ground_vertices()) - 1
            ground = tuple(chr(70+l) for l in range(0, k + 2))
            graphs = [KontsevichGraph({v : {}}, ground_vertices=tuple(v),
                                      immutable=True) for v in ground]
            arguments = [self.parent()([(1, h)]) for h in graphs]
            diff += arguments[0]*self.subs(*(arguments[1:]))
            for i in range(0, k + 1):
                new_arguments = arguments[0:i]
                new_arguments += [arguments[i]*arguments[i+1]]
                new_arguments += arguments[i+2:] if i+2 <= k+1 else []
                diff += (-(-1)**i)*self.subs(*new_arguments)
            diff += (-1)**k * self.subs(*(arguments[0:-1])) * arguments[-1]
        return diff

    def self_action(self, target, insert=False):
        """
        Action of a wedge with one leg on a fixed target and the other on
        the whole graph.
        If ``insert`` is True, replace ``target`` by the top of the wedge.
        """
        self_action_terms = []
        for (c,g) in self:
            n = len(g.internal_vertices())
            for v in g:
                if v == target:
                    continue                      # skip multiple edges (zero) graphs
                self_action_terms.append((c, g.add_wedge(target, v, insert)))
        return self.parent()(self_action_terms)

    def in_degrees(self):
        """
        In-degrees of ground vertices of terms.
        """
        for (c,g) in self:
            yield tuple(g.in_degree(v) for v in g.ground_vertices())

    def __getitem__(self, indegrees):
        """
        Sum of terms with specified in-degrees of the ground vertices.
        """
        indegree_terms = []
        for (c,g) in self:
            if tuple(g.in_degree(v) for v in g.ground_vertices()) == indegrees:
                indegree_terms.append((c, g))
        return self.parent()(indegree_terms)


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
        if isinstance(terms, KontsevichGraph):
            terms = [(1, terms)]
        if isinstance(terms, KontsevichGraphSum):
            terms = terms._terms
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
        KG = KontsevichGraph([(1, 'F', 'L'), (1, 'G', 'R')],
                             ground_vertices=('F', 'G'),
                             immutable=True)
        return self.element_class(self, [(self.base_ring().an_element(), KG)])

    def jacobiator(self, f, g, h, on=None):
        """
        Return the Jacobiator with ground vertices ``f``, ``g``, ``h``
        in ``self``. If ``on`` is not None, return the Jacobiator on
        top of the KontsevichGraph ``on`` with target vertices ``f``,
        ``g``, ``h``, while keeping the ground vertices of ``on``.
        """
        n = 0
        if on:
            n = max(on.internal_vertices())
        else:
            assert not (1 in (f,g,h) or 2 in (f,g,h))
        Jacobi = KontsevichGraph([(n+1, f, 'L'), (n+1, g, 'R'), (n+2, n+1, 'L'),
                                  (n+2, h, 'R')], ground_vertices=(f, g, h),
                                  immutable=True)
        terms = []
        for cyclic_permutation in ((f,g,h), (g,h,f), (h,f,g)):
            graph = Jacobi.relabel({f : cyclic_permutation[0],
                                    g : cyclic_permutation[1],
                                    h : cyclic_permutation[2]}, inplace=False)
            if on:
                graph = graph.copy(immutable=False)
                for v in on.ground_vertices():
                    if not v in graph:
                        graph.add_vertex(v)
                graph.ground_vertices(on.ground_vertices())
                graph = graph.union(on)
                graph = graph.copy(immutable=True)
            else:
                graph.ground_vertices((f, g, h))
            terms.append((self.base_ring()(1), graph))
        return self.element_class(self, terms)
