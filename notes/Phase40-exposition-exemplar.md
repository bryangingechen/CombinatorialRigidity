# The pinned exemplar for round 3, `40-exposition` (frozen)

The PI-approved sample section, `sec:main-component-splitoff` of
`blueprint/src/chapter/main-component.tex`, copied verbatim at task 2 (Stop 1 closed
2026-10-03; the PI's entry is in `notes/Phase40-exposition.md` *Autopilot: for the PI*). It
fixes the register, depth and evidence bar for tasks 3–26, together with defaults (a)–(f) in
that log's *Decisions*. The block below is altered only to correct a verified factual error. The
live text in the chapter may change later; this copy does not follow it.

---BEGIN EXEMPLAR---
```tex
\subsection{Splitting off a body of degree two}
\label{sec:main-component-splitoff}

This subsection proves the split-off step. Let $x$ be a body of degree
two whose neighbours $a$ and $b$ are not adjacent, and let
$V_1 = V(G) \setminus \{x\}$, so that $a - x - b$ is an open ear on $V_1$
(\cref{sec:main-component-chain}). Splitting off $x$ gives the graph
$G'' = G_x^{ab}$ (\cref{def:graph-operations}): it is $G[V_1]$ together
with a new edge $ab$, which carries the label of $ax$. We show that if
the general configuration of $G''$ attains, then so does that of $G$,
provided that
\[
  \delta \;=\; \operatorname{def}(\tilde G[V_1]) -
  \operatorname{def}(\tilde G[V_1]; a, b) \;\ge\; 5
\]
(\cref{def:deficiency-merged}, at $n = 3$). Here $\delta$ is how far the
deficiency of $G[V_1]$ drops when only partitions with $a$ and $b$ in one
part are counted. The structural coverage applies this step to a chain
$a - x - b$ with $\delta \ge 5$ (\cref{def:pencil-x0-usable-chain}).

The idea is to put $x$ back on the line through $a$ and $b$. Take a
configuration of $G''$ at its target rank, and place the point of $x$ on
the line through the points of $a$ and $b$, distinct from both. We call
this the \emph{special position} of $x$. There the hinges at $ax$ and
$xb$ are nonzero multiples of the hinge at $ab$, and adding $x$ raises
the rank by exactly five (\cref{lem:pencil-splitoff-special-rank}). The
hypothesis $\delta \ge 5$ is what makes five enough: it implies that the
target of $G$ is at most the target of $G''$ plus five.

The special position does not finish the proof. There $a$, $x$ and $b$
are pictured on one line, so the picture is not a main picture of $G$,
and \cref{lem:pencil-x0-one-witness} needs one. We therefore move the
picture of $x$ along a line to a general point, and move the heights
with it so that each closed neighbourhood stays in a plane
(\cref{lem:pencil-splitoff-flexes}, \cref{lem:pencil-splitoff-curve}).
Along this curve the rank falls below its starting value at only finitely
many points (\cref{lem:pencil-curve-limit}), and the picture fails to be
main at only finitely many. Any other point of the curve gives the
configuration that \cref{lem:pencil-x0-one-witness} needs.

Jackson and Jord\'an's proof of their pin-collinear
theorem~\cite{jacksonJordan2008pin} handles the same situation: a vertex
of degree two whose neighbours are not adjacent, where joining the
neighbours by an edge lowers the deficiency of the rest of the graph.
They realize the smaller graph with the new edge by induction, move the
pin of that edge slightly, and then add back the vertex by a 1-extension
and a 0-extension. We reverse the order: we put $x$ back first, at the
special position, where the rank is known exactly, and then move it.
Since we move along a polynomial curve rather than within a small
Euclidean neighbourhood, the argument works over every infinite field.

We begin with the lower semicontinuity of the rank
(\cref{lem:rank-polynomial-of-le-finrank}) along a polynomial curve of
normals.

\begin{lemma}[The rank along a polynomial curve of normals]
  \label{lem:pencil-curve-limit}
  \lean{CombinatorialRigidity.Molecular.PanelHingeFramework.finite_setOf_finrank_lt_of_curve}
  \leanok
  \uses{def:panel-hinge-framework, def:panel-support-extensor,
        def:rigidity-matrix}
  Let $G$ be a finite graph, and let $t \mapsto n(t) = (n_v(t))$ be panel
  normals whose coordinates are polynomials in $t \in K$, such that the
  hinge at every edge of $G$ is nonzero at $t = 0$. Then for all but
  finitely many $t \in K$, the rank of the rigidity matrix of the
  panel-hinge framework on $G$ with normals $n(t)$ is at least its value
  at $t = 0$.
\end{lemma}
\begin{proof}
  \leanok
  \uses{lem:rank-polynomial-of-le-finrank}
  By \cref{lem:rank-polynomial-of-le-finrank} at $n(0)$ there is a
  polynomial $Q$ in the normal coordinates, nonzero at $n(0)$, such that
  the rank is at least its value at $n(0)$ wherever $Q$ is nonzero. The
  polynomial $t \mapsto Q(n(t))$ in one variable is nonzero at $t = 0$, so
  it has finitely many roots, and off them the bound holds.
\end{proof}

The next lemma computes the rank at the special position. It is stated
for panel normals in $K^{k+2}$; configurations are the case $k = 2$,
where $D - 1 = 5$.

\begin{lemma}[The rank at the special position]
  \label{lem:pencil-splitoff-special-rank}
  \lean{Graph.finrank_span_rigidityRows_splitOff_special,
    CombinatorialRigidity.Molecular.BodyHingeFramework.finrank_span_rigidityRows_eq_add_of_motions}
  \leanok
  \uses{def:graph-operations, def:panel-hinge-framework,
        def:rigidity-matrix}
  Let $G$ have an open ear $a - x - b$ on $V_1$ with one interior body,
  and let $G''$ be the splitting-off $G_x^{ab}$
  (\cref{def:graph-operations}) whose new edge $ab$ carries the label of
  the edge $ax$. Let $(n_v)$ be panel normals in $K^{k+2}$ with $n_a$ and
  $n_b$ linearly independent and
  \[
    n_x = (1 - s)\, n_a + s\, n_b, \qquad s \neq 0, 1.
  \]
  Then the rank of the rigidity matrix of the panel-hinge framework on
  $G$ with these normals is that of $G''$ plus $D - 1$, where
  $D = \binom{k+2}{2}$ is the dimension of the screw space.
\end{lemma}
\begin{proof}
  \leanok
  \uses{def:panel-support-extensor, def:hinge-constraint,
        lem:span-rigidityRows-eq-of-motions-eq}
  The panel support extensor is bilinear and alternating
  (\cref{def:panel-support-extensor}), so up to sign the hinges at $ax$
  and $xb$ are $s\,C$ and $(1 - s)\,C$, where $C \neq 0$ is the hinge at
  $ab$ in $G''$; every other edge has the same hinge in $G$ and in $G''$.
  Since $S_x - S_b = (S_x - S_a) + (S_a - S_b)$, a screw assignment $S$ is
  therefore a motion of $G$ if and only if it is a motion of $G''$ with
  $S_x - S_a \in K C$. As $x$ is not a body of $G''$, the map
  $S \mapsto S_x - S_a$ takes the motions of $G''$ onto the screw space,
  so the motions of $G$ have codimension $D - 1$ in those of $G''$. The
  row spaces are the annihilators of the motion spaces
  (\cref{lem:span-rigidityRows-eq-of-motions-eq}), so the ranks differ by
  $D - 1$.
\end{proof}

To choose the special position we need one more lemma. A solution of
the lifting system is a pair $(z, h)$: heights $z$, and for each body
$v$ an affine function $h_v$ that agrees with $z$ on the closed
neighbourhood of $v$ (\cref{def:pencil-weighted-lifting-system}). The
curve needs a special point at which $h_a - h_b$ is nonzero on some
solution for $G[V_1]$, unless $h_a = h_b$ on every solution
(\cref{lem:pencil-splitoff-curve}(1)). Such a point exists unless every
solution has $h_a - h_b$ vanishing on the line through $q_a$ and $q_b$.
The next lemma shows that in that case $h_a = h_b$ on every solution. It
is stated for pairs $(z, h)$, not for heights alone, because at a body of
degree one in $G[V_1]$ the heights do not determine $h_v$.

\begin{lemma}[End planes that all meet over the line of the ends coincide]
  \label{lem:pencil-splitoff-flexes}
  \lean{Graph.planeDiff_eq_zero_of_splitOff}
  \leanok
  \uses{def:graph-operations, def:pencil-weighted-lifting-system,
        def:pencil-lifting-space, def:pencil-admissible-picture}
  Let $G$ have an open ear $a - x - b$ on $V_1$ with one interior body,
  let $G' = G[V_1]$, and let $G''$ be the splitting-off $G_x^{ab}$ whose
  new edge $ab$ carries the label of the edge $ax$. Let $q$ be admissible
  for $G$ and for $G''$, with $\dim L_{G''}(q) \le \dim L_G(q)$. If every
  solution $(z, h)$ of the lifting system of $G'$ at $q$
  (\cref{def:pencil-weighted-lifting-system}) has
  \[
    (h_a - h_b) \cdot (q_a, 1) = 0 \qquad\text{and}\qquad
    (h_a - h_b) \cdot (q_b, 1) = 0,
  \]
  then every such solution has $h_a = h_b$.
\end{lemma}
\begin{proof}
  \leanok
  \uses{lem:pencil-x0-one-witness, lem:pencil-three-points}
  Suppose some solution $y_0$ has $h_a \neq h_b$. The affine function
  $h_a - h_b$ vanishes at $q_a$ and $q_b$, and $q_a$, $q_b$, $q_x$ are
  not collinear, as $q$ is admissible for $G$. So the functional
  $\varphi(z, h) = (h_a - h_b) \cdot (q_x, 1)$ is nonzero at $y_0$.

  We compare the solution spaces of the three lifting systems at $q$.
  First, every solution for $G'$ is one for $G''$. Indeed, the closed
  neighbourhoods of $a$ and $b$ in $G''$ gain $b$ and $a$ respectively,
  and by hypothesis $h_a \cdot (q_b, 1) = h_b \cdot (q_b, 1) = z_b$ and
  $h_b \cdot (q_a, 1) = z_a$. Second, restriction to $V_1$ maps the
  solutions for $G$ injectively into the solutions for $G'$ on which
  $\varphi$ vanishes. A restricted solution is a solution for $G'$, since
  each closed neighbourhood in $G'$ lies inside the one in $G$. And
  $\varphi$ vanishes on it, since $x$ lies in the closed neighbourhoods of
  both $a$ and $b$ in $G$, so $h_a$ and $h_b$ both take the value $z_x$
  at $q_x$. The map is injective: a solution for $G$ that vanishes on
  $V_1$ has $z_x = h_a \cdot (q_x, 1) = 0$, so $h_x$ vanishes at the three
  non-collinear points $q_a, q_x, q_b$, and $h_x = 0$ (as in
  \cref{lem:pencil-three-points}). Since $\varphi(y_0) \neq 0$, the
  solutions for $G$ form a space of smaller dimension than the solutions
  for $G'$, and hence than those for $G''$. At a picture admissible for a
  graph, the solutions form a space of dimension $\dim L(q)$ (the proof of
  \cref{lem:pencil-x0-one-witness}). So $\dim L_G(q) < \dim L_{G''}(q)$, a
  contradiction.
\end{proof}

The last lemma collects three facts used to build the curve.

\begin{lemma}[A line of solutions through the special position]
  \label{lem:pencil-splitoff-curve}
  \lean{CombinatorialRigidity.Molecular.exists_mem_forall_add_smul_eq_zero,
    Graph.mem_liftingSpace_oneEar, Graph.ker_liftingMatrix_congr}
  \leanok
  \uses{def:pencil-weighted-lifting-system, def:pencil-lifting-space,
        def:pencil-admissible-picture}
  \begin{enumerate}
    \item Let $L$ be a subspace of a vector space over $K$, let
      $\varphi_0$ and $\psi$ be linear functionals, and let $y_0 \in L$
      with $\varphi_0(y_0) = 0$. Suppose that $\varphi_0$ is nonzero
      somewhere on $L$, or that $\varphi_0$ and $\psi$ both vanish on $L$.
      Then some $w \in L$ has
      $\varphi_0(y_0 + t w) + t\, \psi(y_0 + t w) = 0$ for every
      $t \in K$.
    \item Let $G$ have an open ear $a - x - b$ on $V_1$ with one interior
      body, and let $q$ be admissible for $G$. If a solution $(z, h)$ of
      the lifting system of $G[V_1]$ at $q$ has
      $(h_a - h_b) \cdot (q_x, 1) = 0$, then the height that agrees with
      $z$ away from $x$ and takes the value $h_a \cdot (q_x, 1)$ at $x$
      lies in $L_G(q)$.
    \item The solutions of the lifting system of a graph $H$ at a picture
      depend only on the picture at the bodies of $H$.
  \end{enumerate}
\end{lemma}
\begin{proof}
  \leanok
  \uses{lem:pencil-three-points, lem:pencil-picture-local}
  (1) If $\varphi_0(W) \neq 0$ for some $W \in L$, take
  $w = \varphi_0(W)^{-1}\bigl(\psi(W)\, y_0 - \psi(y_0)\, W\bigr)$. Then
  $\varphi_0(y_0 + t w) = -t\,\psi(y_0)$ and
  $\psi(y_0 + t w) = \psi(y_0)$. (One finds this $w$ by solving the
  condition on the line $y_0 + K W$ at each $t$. The solution is rational
  in $t$, and as the condition is homogeneous it can be rescaled to clear
  the denominator.) Otherwise $\varphi_0$ and $\psi$ vanish on $L$, and
  $w = 0$ will do.

  (2) At a body $v$ of $V_1$, the closed neighbourhood in $G$ is the one
  in $G[V_1]$, with $x$ added when $v$ is $a$ or $b$. The height agrees
  with $h_v$ on it: at $x$, because $h_a$ and $h_b$ agree at
  $(q_x, 1)$. The closed neighbourhood of $x$ is $\{a, x, b\}$, and every
  height agrees with an affine function on three points
  (\cref{lem:pencil-three-points}).

  (3) Each condition of the lifting system of $H$ reads the picture at a
  member of the closed neighbourhood of a body of $H$, and these are
  bodies of $H$ (as in \cref{lem:pencil-picture-local}).
\end{proof}

\begin{theorem}[Splitting off a body of degree two]
  \label{thm:pencil-x0-splitoff}
  \lean{Graph.X0Attains.of_splitOff}
  \leanok
  \uses{def:pencil-x0-attains, def:pencil-x0-standing,
        def:graph-operations, def:D-deficiency, def:deficiency-merged}
  Let $K$ be infinite and let $G$ satisfy the standing hypotheses
  (\cref{def:pencil-x0-standing}), with an open ear $a - x - b$ on $V_1$
  with one interior body whose ends $a$ and $b$ are not adjacent. Let
  $G''$ be $G$ with $x$ suppressed: the splitting-off $G_x^{ab}$
  (\cref{def:graph-operations}) whose new edge $ab$ carries the label of
  the edge $ax$. Suppose $\operatorname{def}(\tilde G[V_1]; a, b) + 5 \le
  \operatorname{def}(\tilde G[V_1])$ (\cref{def:deficiency-merged},
  \cref{def:D-deficiency}, at $n = 3$). If the general configuration of
  $G''$ attains, then the general configuration of $G$ attains.
\end{theorem}
\begin{proof}
  \leanok
  \uses{lem:splitoff-deficiency-merged, lem:deficiency-ear,
        lem:splitoff-deficiency-reuse, thm:pencil-jj-equality,
        lem:pencil-lifting-space-deficiency,
        lem:pencil-x0-main-picture-open, lem:pencil-x0-one-witness,
        lem:pencil-rank-congr, lem:pencil-curve-limit,
        lem:pencil-splitoff-special-rank, lem:pencil-splitoff-flexes,
        lem:pencil-splitoff-curve}
  \emph{The counts.} The new edge $ab$ lowers by five the value of every
  partition of $V_1$ that separates $a$ and $b$, and by hypothesis the
  other partitions are already five below
  $\operatorname{def}(\tilde G[V_1])$. So
  $\operatorname{def}(\tilde G'') + 5 \le
  \operatorname{def}(\tilde G[V_1])$
  (\cref{lem:splitoff-deficiency-merged}, at $D = 6$). With
  $\operatorname{def}(\tilde G[V_1]) \le \operatorname{def}(\tilde G) + 4$
  (\cref{lem:deficiency-ear}, at $k = 1$) this gives
  $\operatorname{def}(\tilde G'') + 1 \le \operatorname{def}(\tilde G)$.
  Also $\operatorname{def}_2(G'') \le \operatorname{def}_2(G)$
  (\cref{lem:splitoff-deficiency-reuse}, at $n = 2$).

  \emph{The picture.} As $a$ and $b$ are not adjacent, $G''$ is simple
  and each of its closed neighbourhoods has as many members as in $G$, at
  least three. So Jackson and Jord\'an's equality applies to $G''$
  (\cref{thm:pencil-jj-equality}). Take a picture $q$ off the zero sets
  of three nonzero polynomials: that of the attainment at
  $G''$, that of the equality at $G''$, and the main-picture polynomial
  of $G$ (\cref{lem:pencil-x0-main-picture-open}). Then $q$ is admissible
  for $G''$ and a main picture of $G$, some $z'' \in L_{G''}(q)$ gives
  $G''$ its target rank, and
  \[
    \dim L_{G''}(q) \;=\; 3 + \operatorname{def}_2(G'') \;\le\;
    3 + \operatorname{def}_2(G) \;\le\; \dim L_G(q)
  \]
  (\cref{lem:pencil-lifting-space-deficiency}). Let $y_0 = (z'', h)$ be
  a solution of the lifting system of $G''$ at $q$ with heights $z''$.
  It is a solution for $G[V_1]$, and $h_a - h_b$ vanishes at $(q_a, 1)$
  and $(q_b, 1)$, since $ab$ is an edge of $G''$.

  \emph{The special position.} If some solution for $G[V_1]$ has
  $h_a - h_b$ nonzero at $(q_a, 1)$ or at $(q_b, 1)$, then for all but
  at most one $s$ it is nonzero at $(1 - s)(q_a, 1) + s\,(q_b, 1)$.
  Otherwise every solution for $G[V_1]$ has $h_a = h_b$
  (\cref{lem:pencil-splitoff-flexes}). Fix $s \neq 0, 1$ accordingly, put
  $q^0_x = (1 - s) q_a + s\, q_b$, and let
  $\varphi_0(z, h) = (h_a - h_b) \cdot (q^0_x, 1)$ and
  $\psi(z, h) = (h_a - h_b) \cdot (q_x - q^0_x, 0)$. By
  \cref{lem:pencil-splitoff-curve}(1) there is a solution $w$ for
  $G[V_1]$ such that $y(t) = y_0 + t w$ satisfies
  $\varphi_0(y(t)) + t\,\psi(y(t)) = 0$ for every $t$.

  \emph{The curve.} Let $q(t)$ be $q$ with the picture of $x$ moved to
  $q^0_x + t\,(q_x - q^0_x)$, so that $q(1) = q$. As $q(t)$ agrees with
  $q$ on $V_1$, $y(t)$ is a solution for $G[V_1]$ at $q(t)$
  (\cref{lem:pencil-splitoff-curve}(3)), and the identity above says
  that its $h_a - h_b$ vanishes at $(q(t)_x, 1)$. Let $z(t)$ be the
  height of $y(t)$ on $V_1$, extended by $h_a \cdot (q(t)_x, 1)$ at $x$.
  The points of the configuration $(q(t), z(t))$ are polynomials in $t$.
  At $t = 0$ they are at the special position:
  $p_x = (1 - s) p_a + s\, p_b$, because $h_a$ takes the values $z''_a$
  and $z''_b$ at $q_a$ and $q_b$. Also $p_a$ and $p_b$ are independent, as
  $q_a \neq q_b$. Every hinge of $G$ is nonzero at $t = 0$: $q^0_x$
  differs from $q_a$ and $q_b$ as $s \neq 0, 1$, and every other edge is
  an edge of $G''$. So at $t = 0$ the rank of $G$ is that of $G''$ at
  $(q, z'')$ plus five
  (\cref{lem:pencil-splitoff-special-rank}, \cref{lem:pencil-rank-congr}).

  \emph{A good parameter.} By \cref{lem:pencil-curve-limit}, the rank of
  $G$ at $(q(t), z(t))$ is at least its value at $t = 0$ for all but
  finitely many $t$. The main-picture polynomial of $G$ at $q(t)$ is a
  polynomial in $t$, nonzero at $t = 1$, so $q(t)$ is a main picture of
  $G$ for all but finitely many $t$. Take $t$ outside both finite sets.
  Then $z(t) \in L_G(q(t))$ (\cref{lem:pencil-splitoff-curve}(2)), and
  $(q(t), z(t))$ has rank at least
  \[
    6(|V_1| - 1) - \operatorname{def}(\tilde G'') + 5 \;\ge\;
    6(|V(G)| - 1) - \operatorname{def}(\tilde G),
  \]
  as $|V(G)| = |V_1| + 1$. By \cref{lem:pencil-x0-one-witness} the
  general configuration of $G$ attains.
\end{proof}

```
---END EXEMPLAR---
