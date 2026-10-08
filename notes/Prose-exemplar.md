# The pinned exemplar for PROSE, rounds 1–4 (frozen)

The PI-approved sample section, *Preservation of the Laman property* in
`blueprint/src/chapter/henneberg.tex` (lines 159–258 at `e9e3f37d`, from its `\subsection`
through the `\end{proof}` of `thm:typeI-isLaman-iff`), copied verbatim at task 4 of round 1,
`prose-laman`. The PI approved it at Stop 1 on 2026-10-07 with one revision, made before this
copy: the sentence "These facts are classical." is gone. The PI's entry is in
`notes/Prose-laman-cleanup.md` *Autopilot: for the PI*, and that log's *Decisions* transcribe it.
It fixes the register, depth and evidence bar for round 1's slices (tasks 5.1–5.16) and for rounds
2–4 (`notes/Prose.md` §2), beside `40-exposition`'s exemplar `notes/Phase40-exposition-exemplar.md`
and `blueprint/AUTHORING.md` principles A–F. It shows principle B's clause of 2026-10-07: a
construction in a statement is written in words ("Let $G'$ be obtained from $G$ by …"), not as its
Lean encoding. The block below is altered only to correct a verified factual error. The live text
in the chapter may change later; this copy does not follow it.

---BEGIN EXEMPLAR---
```tex
\subsection{Preservation of the Laman property}

We show that both moves preserve the Laman property, and that the
Type~I move also reflects it. Jord\'an~\cite{jordan2016} proves the
sparsity part of these facts as Lemmas 2.1.5 and 2.1.4(a), where the
two moves are called the $0$-extension and the $1$-extension.

\begin{theorem}[Type~I preserves the Laman property]
  \label{thm:typeI-isLaman}
  \lean{SimpleGraph.Henneberg.typeI_isLaman}
  \leanok
  \uses{def:typeI, def:isLaman, lem:typeI-edgeSet-ncard}
  Let $G$ be a Laman graph and let $a \ne b$ be vertices of $G$. Let
  $G'$ be obtained from $G$ by the Type~I move at $a$ and $b$. Then
  $G'$ is Laman.
\end{theorem}
\begin{proof}
  \leanok
  Let $v$ be the new vertex of $G'$. The graph $G'$ has one more vertex
  than $G$ and two more edges (\cref{lem:typeI-edgeSet-ncard}), so
  $|E(G')| + 3 = 2|V(G')|$ follows from $|E(G)| + 3 = 2|V(G)|$.

  For $(2,3)$-sparsity (\cref{def:isSparse}) we show that every set $X$
  of at least two vertices of $G'$ spans at most $2|X| - 3$ edges. Let
  $X_0 = X \setminus \{v\}$. The edges of $G'$ inside $X$ are the edges
  of $G$ inside $X_0$, together with those of the new edges $va$ and
  $vb$ that lie inside $X$. If $v \notin X$, then $X = X_0$, and the
  bound holds because $G$ is sparse. Otherwise $|X| = |X_0| + 1$. If
  $|X_0| = 1$, then $X_0$ spans no edge and at most one new edge lies
  inside $X$, so $X$ spans at most $1 = 2|X| - 3$ edges. If
  $|X_0| \ge 2$, then
  \[
    |\edgesIn[G']{X}| \;\le\; |\edgesIn{X_0}| + 2
    \;\le\; (2|X_0| - 3) + 2 \;=\; 2|X| - 3.
  \]
\end{proof}

\begin{theorem}[Type~II preserves the Laman property]
  \label{thm:typeII-isLaman}
  \lean{SimpleGraph.Henneberg.typeII_isLaman}
  \leanok
  \uses{def:typeII, def:isLaman, lem:typeII-edgeSet-ncard}
  Let $G$ be a Laman graph, let $ab$ be an edge of $G$, and let
  $c \ne a, b$ be a vertex of $G$. Let $G'$ be obtained from $G$ by the
  Type~II move on $ab$ and $c$. Then $G'$ is Laman.
\end{theorem}
\begin{proof}
  \leanok
  Let $v$ be the new vertex of $G'$. The move deletes $ab$ and adds
  $va$, $vb$ and $vc$, so $G'$ has one more vertex than $G$ and two more
  edges (\cref{lem:typeII-edgeSet-ncard}). The count follows as in
  \cref{thm:typeI-isLaman}.

  For sparsity, let $X$ and $X_0$ be as in the proof of
  \cref{thm:typeI-isLaman}. The edges of $G'$ inside $X$ are the edges
  of $G$ inside $X_0$ other than $ab$, together with those of $va$,
  $vb$ and $vc$ that lie inside $X$. The cases $v \notin X$ and
  $|X_0| = 1$ go as before. Suppose that $v \in X$ and $|X_0| \ge 2$.
  If $a$ and $b$ both lie in $X_0$, then $ab$ is an edge of $G$ inside
  $X_0$ that $G'$ does not have, and at most three new edges lie inside
  $X$. Otherwise one of $va$ and $vb$ does not lie inside $X$, so at
  most two new edges do. In both cases
  $|\edgesIn[G']{X}| \le |\edgesIn{X_0}| + 2 \le 2|X| - 3$.
\end{proof}

The reverse decomposition (\cref{sec:henneberg-decomp}) needs the
converse of \cref{thm:typeI-isLaman}, to show that removing a vertex of
degree two from a Laman graph leaves a Laman graph.

\begin{theorem}[Type~I reflects the Laman property]
  \label{thm:typeI-reverse-isLaman}
  \lean{SimpleGraph.Henneberg.typeI_reverse_isLaman}
  \leanok
  \uses{def:typeI, def:isLaman, lem:typeI-edgeSet-ncard}
  Let $G$ be a finite graph and let $a \ne b$ be vertices of $G$. Let
  $G'$ be obtained from $G$ by the Type~I move at $a$ and $b$. If $G'$
  is Laman, then $G$ is Laman.
\end{theorem}
\begin{proof}
  \leanok
  Let $v$ be the new vertex of $G'$. Both new edges contain $v$, so a
  set of vertices of $G$ spans the same edges in $G'$ as in $G$. Hence
  $G$ is $(2,3)$-sparse because $G'$ is. The count follows from
  \cref{lem:typeI-edgeSet-ncard}, as in \cref{thm:typeI-isLaman}.
\end{proof}

\begin{theorem}[Type~I preserves and reflects the Laman property]
  \label{thm:typeI-isLaman-iff}
  \lean{SimpleGraph.Henneberg.typeI_isLaman_iff}
  \leanok
  \uses{thm:typeI-isLaman, thm:typeI-reverse-isLaman}
  Let $G$ be a finite graph and let $a \ne b$ be vertices of $G$. Let
  $G'$ be obtained from $G$ by the Type~I move at $a$ and $b$. Then
  $G'$ is Laman if and only if $G$ is Laman.
\end{theorem}
\begin{proof}
  \leanok
  Combine \cref{thm:typeI-isLaman} and
  \cref{thm:typeI-reverse-isLaman}.
\end{proof}
```
---END EXEMPLAR---
