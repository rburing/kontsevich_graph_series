r"""
Kontsevich graphs

"""
from sage.graphs.digraph import DiGraph
from sage.groups.perm_gps.permgroup_named import SymmetricGroup
from sage.structure.factorization import Factorization
from sage.rings.integer import Integer
from itertools import product, ifilter
# for weights:
from sage.tensor.coordinate_patch import CoordinatePatch
from sage.tensor.differential_forms import DifferentialForms
from sage.tensor.differential_form_element import DifferentialForm
from sage.symbolic.ring import SR
from sage.symbolic.pynac import I
from sage.functions.trig import arctan

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

def kontsevich_graph_from_latex(operator):
    """
    Build Kontsevich graph from multi-differential operator as a LaTeX string.
    """
    tokens = operator.split(' ')
    edges = []
    ground_vertices = []
    internal_vertices = []
    for t in tokens:
        if len(t) == 10 and t[0:8] == '\\partial':
            source = None
            for v in internal_vertices:
                if t[9] in v:
                    source = v
            edges.append((source, None, t[9]))
        elif len(t) == 11 and t[0:6] == '\\alpha':
            target = t[8:10]
            internal_vertices.append(target)
            for k in range(0, len(edges)):
                (s,t,l) = edges[k]
                if t == None:
                    t = target
                if l in target:
                    s = target
                edges[k] = (s,t,l)
        else:
            target = t
            ground_vertices.append(t)
            for k in range(0, len(edges)):
                (s,t,l) = edges[k]
                if t == None:
                    t = target
                edges[k] = (s,t,l)
    # relabeling
    relabeling = dict(zip(internal_vertices, range(1, len(internal_vertices)+1)))
    for k in range(0, len(edges)):
        (s,t,l) = edges[k]
        l = 'L' if l == s[0] else 'R'
        s = relabeling[s]
        t = relabeling[t] if t in relabeling else t
        edges[k] = (s,t,l)
    return edges, tuple(ground_vertices)

class KontsevichGraph(DiGraph):
    def __init__(self, *args, **kwargs):
        """
        Kontsevich graph.

        INPUT:

         - All the usual arguments to DiGraph.
         - ``ground_vertices`` -- a tuple of vertices to be ground vertices

         - Shorthand: a tuple of strings as the only argument, to produce the
           Kontsevich graph with just those ground vertices.
         - LaTeX: a LaTeX string as the only argument, to convert an expression
           for an appropriate multi-differential operator into a Kontsevich graph.

        OUTPUT:

        A KontsevichGraph object.

        EXAMPLES::

            sage: KontsevichGraph(ground_vertices=())
            Kontsevich graph with 0 vertices on 0 ground vertices
            sage: KontsevichGraph(('F',))
            Kontsevich graph with 0 vertices on 1 ground vertices
            sage: KontsevichGraph(('F','G'))
            Kontsevich graph with 0 vertices on 2 ground vertices
            sage: KontsevichGraph({'F' : {}, 'G' : {}, 1 : {'F' : 'L', \
            ....:                  'G' : 'R'}}, ground_vertices=('F', 'G'))
            Kontsevich graph with 1 vertices on 2 ground vertices
            sage: KontsevichGraph('\\alpha^{ab} \\partial_a F \\partial_b G')
            Kontsevich graph with 1 vertices on 2 ground vertices
        """
        # Edge labels are important in equality testing:
        kwargs['weighted'] = True
        # No multiple edges:
        kwargs['multiedges'] = False

        latex = len(args) == 1 and isinstance(args[0], str)
        if latex:
            edges, ground_vertices = kontsevich_graph_from_latex(args[0])
            args = [edges]
            kwargs['ground_vertices'] = ground_vertices

        shorthand = len(args) == 1 and isinstance(args[0], tuple) and \
                    all(isinstance(v, str) for v in args[0])
        if shorthand:
            ground_vertices = args[0]
            args = [{v : {} for v in ground_vertices}]
            kwargs['ground_vertices'] = ground_vertices

        copying = len(args) == 1 and isinstance(args[0], KontsevichGraph)
        if not copying and not 'ground_vertices' in kwargs:
            raise TypeError('KontsevichGraph() needs keyword argument ' +
                    'ground_vertices, or an existing KontsevichGraph ' +
                    'as the first argument, or a tuple of ground vertices ' +
                    'as the first argument, or a LaTeX string as the first ' +
                    'argument')
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
            sage: KG = KontsevichGraph(('F','G','H')); KG.ground_vertices()
            ('F', 'G', 'H')

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
        return tuple(k for (k,v) in sorted(self.get_vertices().items(), \
                                           key = lambda (v,k) : k) \
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
        
    def show(self, **kwargs):
        """
        Show the Kontsevich graph.
        """
        plot_kwargs = {}
        if 'indices' in kwargs:
            plot_kwargs['indices'] = kwargs['indices']
            del kwargs['indices']
        return self.plot(**plot_kwargs).show(**kwargs)

    def plot(self, **kwargs):
        """
        Return a graphics object representing the Kontsevich graph.

        INPUT:

        - ``edge_labels`` (boolean, default True) -- if True, show edge labels.
        - ``indices`` (boolean, default False) -- if True, show indices as
          edge labels instead of L and R; see :meth:`._latex_`.
        """
        if not 'edge_labels' in kwargs:
            kwargs['edge_labels'] = True        # show edge labels by default
        if 'indices' in kwargs:
            del kwargs['indices']
            KG = DiGraph(self)
            for (k,e) in enumerate(self.edges()):
                KG.set_edge_label(e[0], e[1], chr(97 + k))
            return KG.plot(**kwargs)
        return DiGraph.plot(self, **kwargs)

    def union(self, other, same_ground=True):
        """
        Return the union of self and other.
        """
        if same_ground:
            assert self.ground_vertices() == other.ground_vertices()
            new_ground = self.ground_vertices()
        else:
            new_ground = self.ground_vertices() + other.ground_vertices()
        G = super(KontsevichGraph, self).union(other)
        immutable = getattr(self, '_immutable', False) and \
                    getattr(other, '_immutable', False)
        return KontsevichGraph(G, ground_vertices=new_ground, \
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

        def all_of_them():
            for sigma in SymmetricGroup(self.internal_vertices()):
                yield self.relabel(lambda v: sigma(v) \
                                             if v in self.internal_vertices() \
                                             else v, inplace=False)
        return filter_unique(all_of_them(), key = lambda KG:
                             DiGraph(KG, weighted=True, immutable=True))

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
        old_ground = self.ground_vertices()
        mirror = self.copy(immutable=False)
        relabeling = dict(zip(self.internal_vertices(),
                              self.internal_vertices()))
        relabeling.update(dict(zip(self.ground_vertices(),
                                   reversed(self.ground_vertices()))))
        mirror.relabel(relabeling)
        mirror.ground_vertices(old_ground)
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
        if not isinstance(other, KontsevichGraph):
            return False
        if len(self) != len(other): return False
        if len(self.internal_vertices()) != len(other.internal_vertices()):
            return False
        for KG in other.internal_vertex_relabelings():
            if DiGraph.__eq__(self, KG):
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
        floorless = self.copy(immutable=False)
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
        floorless = self.copy(immutable=False)
        floorless.delete_vertices(self.ground_vertices())
        return len(floorless.connected_components()) == 1

    def internal_vertex_multiplicity(self):
        """
        The number of different unlabeled DiGraphs (with different internal
        vertex labeling) that represent this KontsevichGraph.
        """
        return len(set([DiGraph(g, weighted=False, immutable=True)
                        for g in self.internal_vertex_relabelings()]))

    def edge_multiplicity(self):
        """
        The number of different Kontsevich graphs obtained by swapping
        the edges coming out of internal vertices.
        """
        return len(list(self.edge_relabelings()))

    def multiplicity(self):
        """
        The number of terms equal to w(self)*self when taking a sum over all
        Kontsevich graphs, sometimes double-counting equal edge relabelings.

        EXAMPLES::

            sage: n = 2
            sage: sum(g.multiplicity() for g in kontsevich_graphs(n, \
            ....:     modulo_edge_labeling=True)) == (n*(n+1))^n
            True
        """
        return self.internal_vertex_multiplicity() * \
               2**len(self.internal_vertices())

    def attach(self, *graph_attachments):
        """
        Attach graphs to the ground vertices in the specified manner.

        INPUT:

        - ``graph_attachments`` -- a list of (graph, attachment) pairs, where
          an attachment is a source : destination dictionary of of vertices.
          The length of the list should equal the number of ground vertices.
          The graphs should all have distinct ground vertices.

        OUTPUT:

        The Kontsevich graph constructed by attaching the input graphs to the
        ground vertices in the manner specified. The new ground vertices are
        the concatenation of the input ground vertices.
        """
        graphs, attachments = zip(*graph_attachments)
        assert len(graph_attachments) == len(self.ground_vertices())
        assert all(g.internal_vertices_normalized() for g in graphs)
        assert all(isinstance(a, dict) for a in attachments)
        assert len(graphs) == 1 or \
            not set.intersection(*[set(g.ground_vertices()) for g in graphs])
        import operator
        new_ground = reduce(operator.add, [g.ground_vertices() for g in graphs])
        # Compute the offsets at which the numbering of the attachments'
        # internal vertices should start.
        sizes = [len(g.internal_vertices()) for g in graphs]
        offsets = [len(self.internal_vertices()) + p \
                   for p in partial_sums(sizes)]
        # Relabel attachments.
        attachment_graphs = [graphs[n].relabel({v : v + offsets[n] \
                               for v in graphs[n].internal_vertices()}, \
                               inplace=False) \
                             for n in range(0, len(self.ground_vertices()))]
        # Compute new attachment points.
        attachment_points = [{src : dst + offsets[n] \
                                    if dst in graphs[n].internal_vertices()
                                    else dst
                              for (src, dst) in attachments[n].iteritems()}
                             for n in range(0, len(self.ground_vertices()))]
        G = self.copy(immutable=False)
        G.relabel({v : 'old %s' % v for v in G.ground_vertices()})
        old_ground = G.ground_vertices()
        for g in attachment_graphs:
            G = DiGraph.union(G,g)
        for n in range(0, len(self.ground_vertices())):
            for src in G.neighbors_in(old_ground[n]):
                label = G.edge_label(src, old_ground[n])
                G.add_edge(src, attachment_points[n][src], label)
            G.delete_vertex(old_ground[n])
        return KontsevichGraph(G, ground_vertices=new_ground, immutable=True)

    def add_wedge(self, left, right, insert=False):
        """
        Add a wedge with targets ``left`` and ``right``.
        If ``insert`` is True, replace ``left`` by the top of the wedge.

        EXAMPLES::

            sage: KontsevichGraph(('F','G')).add_wedge('F','G')
            Kontsevich graph with 1 vertices on 2 ground vertices
        """
        n = len(self.internal_vertices())
        wedge = DiGraph([(n + 1, left, 'L'), (n + 1, right, 'R')])
        graph = DiGraph.union(self, wedge)
        if insert:
            for src in list(graph.neighbors_in(left)):
                if src == n + 1:
                    continue
                label = graph.edge_label(src, left)
                graph.delete_edge(src, left)
                graph.add_edge(src, n + 1, label)
        return KontsevichGraph(graph, immutable=True,
                               ground_vertices=self.ground_vertices())

    def _latex_(self):
        """
        Multi-differential operator associated to the Kontsevich graph.

        Summation over all indices is implied.
        """
        index = {e : chr(97+k) for (k,e) in enumerate(self.edges())}
        partials = {v : ' '.join('\\partial_%s' % index[e]
                                 for e in self.incoming_edges(v)) + ' '
                        if self.in_degree(v) > 0 else ''
                    for v in self}
        bivector = {v : '\\alpha^{%s%s}' % tuple(index[e]
                                             for e in self.outgoing_edges(v))
                    for v in self.internal_vertices()}
        return ' '.join('%s%s' % (partials[v], bivector[v])
                        for v in self.internal_vertices()) + ' ' + \
               ' '.join('%s%s' % (partials[v], v)
                        for v in self.ground_vertices())

    def weight_integrand(self, simplify_factor=True):
        """
        Weight integrand as a rational function.

        The Jacobian determinant of some coordinate transformation.
        """
        def arg(x,y):
            return arctan(y/x) # up to a constant, but it doesn't matter
        def phi(x,y,a,b):
            z = (a+I*b-x-I*y)*(a - I*b - x - I*y)
            w = z.real()
            q = z.imag()
            return arg(w,q).full_simplify()
        n = len(self.internal_vertices())
        coordinates = lambda v: SR.var(chr(97+2*(v-1)) + ',' + chr(97+2*(v-1)+1)) \
                                if v in self.internal_vertices() else \
                                [(0,0), (1,0)][self.ground_vertices().index(v)]
        internal_coordinates = sum((list(coordinates(v)) for v in
                                    sorted(self.internal_vertices())), [])
        U = CoordinatePatch(internal_coordinates)
        F = DifferentialForms(U)
        psi = 0
        two_forms = []
        for v in self.internal_vertices():
            x,y = coordinates(v)
            outgoing_edges = self.outgoing_edges([v])
            left_target = filter(lambda (x, y, z): z == 'L', outgoing_edges)[0][1]
            right_target = filter(lambda (x, y, z): z == 'R', outgoing_edges)[0][1]
            one_forms = []
            for target in [left_target, right_target]:
                a,b = coordinates(target)
                one_form = DifferentialForm(F, 1)
                for v in internal_coordinates:
                    index = internal_coordinates.index(v)
                    one_form[index] = phi(x,y,a,b).diff(v)
                    if simplify_factor:
                        one_form[index] = SR(one_form[index]).full_simplify()
                one_forms.append(one_form)
            two_form = one_forms[0]*one_forms[1]
            two_forms.append(two_form)
        import operator
        two_n_form = reduce(operator.mul, two_forms, 1)
        return two_n_form[range(0,2*n)]


def kontsevich_graphs(n, m=2, ground_vertices=None, cycles=True, unique=False,
                      modulo_edge_labeling=False, prime=None,
                      zero=None, modulo_mirror_images=False,
                      positive_differential_order=None):
    """
    Generate KontsevichGraphs with ``n`` internal vertices labeled
    1, ..., n, and ``m`` ground vertices labeled 'F', 'G', ...,
    or labeled by ``ground_vertices`` if it's not ``None``.

    INPUT::

    - ``n`` (integer) -- number of internal vertices.
    - ``m`` (integer, default 2) -- number of ground vertices.
    - ``ground_vertices`` (tuple, default None) -- ground vertices,
      overrides ``m`` if not None.
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
    - ``positive_differential_order`` (boolean, default None): whether to
      yield only graphs whose ground vertices have in-degree > 0
      (None is indifferent).

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

    if not ground_vertices:
        ground_vertices = tuple(chr(70+k) for k in range(0,m))

    internal_vertices = range(1,n+1)
    H = KontsevichGraph({v : {} for v in ground_vertices}, weighted=True,
                        ground_vertices=ground_vertices, immutable=False)
    H.add_vertices(internal_vertices)

    if n == 0:
        return iter([H.copy(immutable=True)])

    def all_of_them():
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
            yield G.copy(immutable=True)

    it = all_of_them()

    # First filter according to properties independent of labeling
    # (these are cheap to test)
    if not cycles:
        it = ifilter(lambda KG: KG.all_simple_cycles() == [], it)

    if prime is not None:
        it = ifilter(lambda KG: KG.is_prime() == prime, it)

    if zero is not None:
        it = ifilter(lambda KG: KG.is_zero() == zero, it)

    if positive_differential_order is not None:
        if positive_differential_order:
            it = ifilter(lambda KG: all(KG.in_degree(v) > 0 \
                                        for v in KG.ground_vertices()), it)
        else:
            it = ifilter(lambda KG: 0 in [KG.in_degree(v) \
                                          for v in KG.ground_vertices()], it)

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
