r"""
Kontsevich graphs

"""
from sage.graphs.digraph import DiGraph
from sage.groups.perm_gps.permgroup_named import SymmetricGroup
from sage.structure.factorization import Factorization
from sage.rings.integer import Integer
from itertools import product, ifilter

def filter_unique(it, key = lambda x : x):
    seen = set()
    for el in it:
        k = key(el)
        if not k in seen:
            seen.add(k)
            yield el

def partial_sums(iterable):
    total = 0
    yield total
    for element in iterable:
        total += element
        yield total

class KontsevichGraph(DiGraph):
    def __init__(self, *args, **kwargs):
        """
        Kontsevich graph.

        INPUT:

         - All the usual arguments to DiGraph.
         - ``ground_vertices`` -- a tuple of vertices to be ground vertices

        OUTPUT:

        A KontsevichGraph object.

        EXAMPLES::

            sage: KontsevichGraph(ground_vertices=())
            Kontsevich graph with 0 vertices on 0 ground vertices
            sage: KontsevichGraph({'F' : {}, 'G' : {}, 1 : {'F' : 'L', \
            ....:                  'G' : 'R'}}, ground_vertices=('F', 'G'))
            Kontsevich graph with 1 vertices on 2 ground vertices
        """
        # Edge labels are important in equality testing:
        kwargs['weighted'] = True
        # No multiple edges:
        kwargs['multiedges'] = False
        copying = len(args) == 1 and isinstance(args[0], KontsevichGraph)
        if not copying and not 'ground_vertices' in kwargs:
            raise TypeError('KontsevichGraph() needs keyword argument ' +
                    'ground_vertices, or an existing KontsevichGraph ' +
                    'as the first argument.')
        if 'ground_vertices' in kwargs:
            ground_vertices = kwargs['ground_vertices']
            del kwargs['ground_vertices']
        else: # if copying:
            ground_vertices = args[0].ground_vertices()

        super(KontsevichGraph, self).__init__(*args, **kwargs)
        self.ground_vertices(ground_vertices)
    
    def ground_vertices(self, vs=None):
        """
        Return and possibly set the ground vertices.

        INPUT:

         - ``vs`` -- if not None, then this becomes the new tuple of
           ground vertices.

        OUTPUT:

        The tuple of current ground vertices.

        EXAMPLES::

            sage: KG = KontsevichGraph({'F' : {}, 'G' : {}, 1 : {'F' : 'L', \
            ....: 'G' : 'R'}}, ground_vertices=('F', 'G'))
            sage: KG.ground_vertices()
            ('F', 'G')
            sage: KG.ground_vertices(('F',))
            ('F',)

        .. NOTE::
            
            Ground vertices of immutable KontsevichGraphs can also be changed,
            as a consequence of the implementation.
        """
        if not vs is None:
            if not isinstance(vs, tuple):
                raise TypeError('Input must be a tuple of vertices.')
            if not all(v in self for v in vs):
                raise ValueError('Input vertices must exist in the ' +
                                 'Kontsevich graph.')
            if not all(self.out_degree(v) == 0 for v in vs):
                raise ValueError('Prospective ground vertices must have ' + 
                                 'out-degree zero.')
            self.set_vertices({v : None for v in self})
            self.set_vertices({v : n for (v,n) in zip(vs, range(0,len(vs)))})
        return tuple(k for (k,v) in sorted(self.get_vertices().items()) \
                     if not v is None)
    
    def internal_vertices(self):
        """
        Return the internal vertices.
        """
        return sorted([v for v in self if not v in self.ground_vertices()])

    def _repr_(self):
        n = len(self.internal_vertices())
        m = len(self.ground_vertices())
        return 'Kontsevich graph with %d vertices on %d ground vertices' % \
               (n, m)
        
    def show(self, *args, **kwargs):
        """
        Show the Kontsevich graph.
        """
        if not 'edge_labels' in kwargs:
            kwargs['edge_labels'] = True        # show edge labels by default
        return super(KontsevichGraph, self).show(*args, **kwargs)

    def union(self, other):
        """
        Return the union of self and other.
        """
        G = super(KontsevichGraph, self).union(other)
        immutable = getattr(self, '_immutable', False) and \
                    getattr(other, '_immutable', False)
        ground_vertices = tuple(set(self.ground_vertices()) | \
                                set(other.ground_vertices()))
        return KontsevichGraph(G, ground_vertices=ground_vertices, \
                               immutable=immutable)

    def normalize_vertex_labels(self):
        """
        Label internal vertices 1, ...,  n.
        Label external vertices F, G, ...
        """
        relabeling = {v : n + 1 for (n, v) in \
                      enumerate(self.internal_vertices())}
        relabeling.update({v : chr(70 + n) for (n, v) in \
                           enumerate(self.ground_vertices())})
        self.relabel(relabeling)

    def internal_vertices_normalized(self):
        """
        Whether the internal vertices are equal to 1, ..., n.
        """
        n = len(self.internal_vertices())
        return self.internal_vertices() == range(1, n + 1)

    def internal_vertex_relabelings(self):
        """
        Yield all possible internal vertex relabelings as Kontsevich graphs.
        """
        assert self.internal_vertices_normalized(), \
               "Internal vertices should be normalized."

        for sigma in SymmetricGroup(self.internal_vertices()):
            G = DiGraph(self, weighted=True, immutable=False)
            G.relabel(lambda v: sigma(v) if v in self.internal_vertices() \
                                else v)
            yield KontsevichGraph(G, ground_vertices=self.ground_vertices(), \
                                  immutable=True)

    def edge_labels_normalized(self):
        """
        Whether the edge labels are all equal to L or R.
        """
        return len(self.edges()) == 0 or \
               set(l for (u,v,l) in self.edges()) == set(['L', 'R'])

    def edge_relabelings(self, signs=False):
        """
        Yield all possible edge relabelings as Kontsevich graphs.
        """
        assert self.internal_vertices_normalized(), \
               "Internal vertices should be normalized."
        assert self.edge_labels_normalized(), \
                "Edge labels should be normalized."

        def all_of_them():
            for swap in product([True,False],
                                repeat=len(self.internal_vertices())):
                KG = self.copy(immutable=False)
                for v in KG.internal_vertices():
                    if swap[v-1]:
                        KG.swap(v, inplace=True)
                KG = KG.copy(immutable=True)
                if signs:
                    yield (KG, (-1)**(sum(1 if x else 0 for x in swap) % 2))
                else:
                    yield KG
        return filter_unique(all_of_them())

    def is_zero(self):
        """
        Whether there are equal relabelings with opposite signs.
        """
        self_relabeling_signs = []
        for (g,s) in self.edge_relabelings(signs=True):
            if g == self:
                self_relabeling_signs.append(s)
                if len(self_relabeling_signs) > 1:
                    return True
        return False

    def mirror_image(self):
        """
        Return mirror image of self.
        """
        mirror = self.copy(immutable=False)
        relabeling = dict(zip(self.internal_vertices(),
                              self.internal_vertices()))
        relabeling.update(dict(zip(self.ground_vertices(),
                                   reversed(self.ground_vertices()))))
        mirror.relabel(relabeling)
        return mirror.copy(immutable=True)

    def swap(self, internal_vertex, inplace=False):
        """
        Swap labels of outgoing edges of ``internal_vertex``.
        """
        if not internal_vertex in self.internal_vertices():
            raise ValueError, "internal_vertex should be an internal vertex."

        KG = self if inplace else self.copy(immutable=False)
        targets = KG.neighbors_out(internal_vertex)
        assert len(targets) == 2
        [t1,t2] = targets
        l1 = KG.edge_label(internal_vertex, t1)
        l2 = KG.edge_label(internal_vertex, t2)
        KG.set_edge_label(internal_vertex, t1, l2)
        KG.set_edge_label(internal_vertex, t2, l1)
        return KG

    def __eq__(self, other):
        """
        Compare self and other for equality.

        Kontsevich graphs are considered equal if the underlying DiGraphs
        differ only in their internal vertex labeling.
        """
        assert self.internal_vertices_normalized(), \
               "Internal vertices should be normalized."

        if len(self) != len(other): return False
        if len(self.internal_vertices()) != len(other.internal_vertices()):
            return False
        for KG in other.internal_vertex_relabelings():
            if DiGraph(self, weighted=True) == DiGraph(KG, weighted=True):
                return True
        return False

    def __hash__(self):
        """
        Hash an immutable graph.
        """
        if getattr(self, "_immutable", False):
            return hash(frozenset((tuple(KG.vertices()), tuple(KG.edges())) \
                                  for KG in self.internal_vertex_relabelings()))
        raise TypeError, "graph is mutable, and thus not hashable"

    def __mul__(self, other):
        """
        Return the product of self and other.

        EXAMPLES::

            sage: KG1 = KontsevichGraph({'F' : {}, 'G' : {}, 1 : {'F' : 'L', \
            ....: 'G' : 'R'}}, ground_vertices=('F','G'))
            sage: KG2 = KontsevichGraph({'F' : {}, 'G' : {}, 1 : {'F' : 'L', \
            ....: 'G' : 'R'}, 2 : {'F' : 'L', 'G' : 'R'}}, \
            ....: ground_vertices=('F','G'))
            sage: KG1*KG1 == KG2
            True
        """
        assert isinstance(other, KontsevichGraph)
        assert self.ground_vertices() == other.ground_vertices()
        assert self.internal_vertices_normalized() and \
               other.internal_vertices_normalized()
        sigma = lambda v: v+len(self.internal_vertices()) \
                          if v in other.internal_vertices() \
                          else v
        multiplicand = KontsevichGraph(other, \
                                       ground_vertices=other.ground_vertices())
        multiplicand.relabel(sigma)
        if getattr(self, '_immutable', False):
            multiplicand._immutable = True
        return self.union(multiplicand)

    def __pow__(self, exponent):
        """
        Return the product of ``self`` with itself, ``exponent`` times.

        EXAMPLES::

            sage: KG1 = KontsevichGraph({'F' : {}, 'G' : {}, 1 : {'F' : 'L', \
            ....: 'G' : 'R'}}, ground_vertices=('F','G'))
            sage: KG1^1 == KG1
            True
            sage: KG2 = KontsevichGraph({'F' : {}, 'G' : {}, 1 : {'F' : 'L', \
            ....: 'G' : 'R'}, 2 : {'F' : 'L', 'G' : 'R'}}, \
            ....: ground_vertices=('F','G'))
            sage: KG1^2 == KG2
            True
            sage: KG1^3
            Kontsevich graph with 3 vertices on 2 ground vertices
        """
        assert self.internal_vertices_normalized(), \
               "Internal vertices should be normalized."
        assert isinstance(exponent, int) or isinstance(exponent, Integer)
        assert exponent >= 0
        product = KontsevichGraph({v : {} for v in self.ground_vertices()}, \
                                  ground_vertices=self.ground_vertices())
        for n in range(0,exponent):
            # Make a copy:
            factor = KontsevichGraph(self, \
                                     ground_vertices=self.ground_vertices())
            sigma = lambda v: v+n*len(self.internal_vertices()) \
                              if v in self.internal_vertices() \
                              else v
            factor.relabel(sigma)
            product = product.union(factor)
        if getattr(self, '_immutable', False):
            product = product.copy(immutable=True)
        return product

    def factor(self):
        """
        Return the prime factorization of the graph.

        EXAMPLES::

            sage: KG = KontsevichGraph({'F' : {}, 'G' : {}, 1 : {'F' : 'L', \
            ....: 'G' : 'R'}, 2 : {'F' : 'L', 'G' : 'R'}}, \
            ....: ground_vertices=('F','G'))
            sage: KG.factor()
            (Kontsevich graph with 1 vertices on 2 ground vertices)^2

        ALGORITHM::

        Delete ground vertices; the remaining connected components
        correspond to the prime factors.
        """
        floorless = DiGraph(self, weighted=True, immutable=False)
        floorless.delete_vertices(self.ground_vertices())
        factors = []
        for C in floorless.connected_components():
            P = self.subgraph(vertices=C + list(self.ground_vertices()))
            P_KG = KontsevichGraph(P, ground_vertices=self.ground_vertices())
            P_KG.normalize_vertex_labels()
            factors.append(P_KG)
        return Factorization([(f,1) for f in factors])
        
    def is_prime(self):
        """
        Whether the graph is prime.

        EXAMPLES::

            sage: KontsevichGraph({'F' : {}, 'G' : {}, 1 : {'F' : 'L', \
            ....: 'G' : 'R'}}, ground_vertices=('F','G')).is_prime()
            True
            sage: KontsevichGraph({'F' : {}, 'G' : {}, 1 : {'F' : 'L', \
            ....: 'G' : 'R'}, 2 : {'F' : 'L', 'G' : 'R'}}, \
            ....: ground_vertices=('F','G')).is_prime()
            False

        ALGORITHM::

        Delete ground vertices; count connected components
        (which correspond to prime factors).
        """
        floorless = DiGraph(self, immutable=False)
        floorless.delete_vertices(self.ground_vertices())
        return len(floorless.connected_components()) == 1

    def multiplicity(self):
        """
        The number of different DiGraphs (with different internal vertex
        labeling) that represent this KontsevichGraph.
        """
        return len(set(DiGraph(KG, weighted=True, immutable=True) \
                       for KG in self.internal_vertex_relabelings()))

    def attach(self, *graph_attachments):
        """
        Attach graphs to the ground vertices at specified attachment points.

        INPUT:

        - ``graph_attachments`` -- a list of (graph, attachment point) pairs.
          The length of the list should equal the number of ground vertices.
          The graphs should all have distinct ground vertices.

        OUTPUT:

        The Kontsevich graph constructed by attaching the input graphs to the
        ground vertices. The new ground vertices are the concatenation of the
        input ground vertices.
        """
        graphs, points = zip(*graph_attachments)
        assert len(graph_attachments) == len(self.ground_vertices())
        assert all(g.internal_vertices_normalized() for g in graphs)
        assert not set.intersection(*[set(g.ground_vertices()) for g in graphs])
        import operator
        new_ground = reduce(operator.add, [g.ground_vertices() for g in graphs])
        # Compute the offsets at which the numbering of the attachments'
        # internal vertices should start.
        sizes = [len(g.internal_vertices()) for g in graphs]
        offsets = [len(self.internal_vertices()) + p \
                   for p in partial_sums(sizes)]
        # Relabel attachments.
        attachments = [graphs[n].relabel({v : v + offsets[n] \
                        for v in graphs[n].internal_vertices()}, \
                        inplace=False) \
                       for n in range(0, len(self.ground_vertices()))]
        # Compute new attachment points.
        attachment_points = [points[n] + offsets[n] \
                             if points[n] in graphs[n].internal_vertices() \
                             else points[n] \
                             for n in range(0, len(self.ground_vertices()))]
        G = self.copy(immutable=False)
        G.relabel({v : 'old %s' % v for v in G.ground_vertices()})
        old_ground = G.ground_vertices()
        for g in attachments:
            G = G.union(g)
        for n in range(0, len(self.ground_vertices())):
            for src in G.neighbors_in(old_ground[n]):
                G.add_edge(src, attachment_points[n])
            G.delete_vertex(old_ground[n])
        G.ground_vertices(new_ground)
        return G.copy(immutable=True)


def kontsevich_graphs(n, m=2, cycles=True, unique=False,
                      modulo_edge_labeling=False, prime=None,
                      zero=None, modulo_mirror_images=False,
                      positive_differential_order=False):
    """
    Generate KontsevichGraphs with ``n`` internal vertices and
    ``m`` ground vertices.

    INPUT::

    - ``n`` (integer) -- number of internal vertices.
    - ``m`` (integer, default 2) -- number of ground vertices.
    - ``cycles`` (boolean, default True): whether to yield graphs with cycles.
    - ``unique`` (boolean, default False): if True, yield no duplicate graphs
      (possible duplicates differ only in their internal vertex labeling).
    - ``modulo_edge_labeling`` (boolean, default False): if True, yield only
      one representative of each class of graphs which are equal up to
      edge labeling.
    - ``prime`` (boolean, default None): whether to yield prime graphs
      or non-prime graphs (None is indifferent).
    - ``zero`` (boolean, default None): whether to yield zero or nonzero
      graphs (None is indifferent).
    - ``modulo_mirror_images`` (boolean, default False): whether to yield
      only one of each "pair" of mirror images.
    - ``positive_differential_order`` (boolean, default False): whether to
      yield only graphs whose ground vertices have in-degree > 0.

    EXAMPLES::
        sage: for n in range(1,4):
        ....:     print len(list(kontsevich_graphs(n))) == (n*(n+1))^n
        True
        True
        True
        sage: # how many graphs "look different":
        sage: for n in range(1,4):
        ....:     print len(list(kontsevich_graphs(n, \
        ....:                                      modulo_edge_labeling=True, \
        ....:                                      modulo_mirror_images=True)))
        1
        4
        26
    """
    def all_of_them():
        ground_vertices = tuple(chr(70+k) for k in range(0,m))
        internal_vertices = range(1,n+1)
        H = DiGraph({v : {} for v in ground_vertices}, weighted=True)
        H.add_vertices(internal_vertices)
        def possible_targets(internal_vertex):
            for v,w in product(H.vertices(), repeat=2):
                if not internal_vertex in [v,w] and v != w:
                    yield (v,w)
        for L in product(*[possible_targets(v) for v in internal_vertices]):
            G = H.copy()
            for v in internal_vertices:
                l, r = L[v-1]
                G.add_edge(v, l, 'L')
                G.add_edge(v, r, 'R')
            KG = KontsevichGraph(G, ground_vertices=ground_vertices, \
                                 immutable=True)
            yield KG

    it = all_of_them()

    # First filter according to properties independent of labeling
    # (these are cheap to test)
    if not cycles:
        it = ifilter(lambda KG: KG.all_simple_cycles() == [], it)

    if prime is not None:
        it = ifilter(lambda KG: KG.is_prime() == prime, it)

    if zero is not None:
        it = ifilter(lambda KG: KG.is_zero() == zero, it)

    if positive_differential_order:
        it = ifilter(lambda KG: all(KG.in_degree(v) > 0 \
                                    for v in KG.ground_vertices()), it)

    # Then filter according to properties which depend on the labeling:
    if modulo_mirror_images and not modulo_edge_labeling:
        it = filter_unique(it, key = lambda KG: frozenset([KG,
                                                           KG.mirror_image()]))

    if modulo_edge_labeling and not modulo_mirror_images:
        it = filter_unique(it, key = lambda KG: \
                frozenset(DiGraph(KG1, weighted=False, immutable=True) \
                          for KG1 in KG.internal_vertex_relabelings()))

    if modulo_mirror_images and modulo_edge_labeling:
        it = filter_unique(it, key = lambda KG: \
                frozenset(frozenset([DiGraph(KG1, weighted=False, \
                                             immutable=True), \
                                     DiGraph(KG1.mirror_image(), \
                                             weighted=False, immutable=True)]) \
                          for KG1 in KG.internal_vertex_relabelings()))

    if unique:
        it = filter_unique(it)

    return it
