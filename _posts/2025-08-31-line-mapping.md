---
layout: post
title: "Can you spot the Error in this proof of the 'standard' Line-to-Line Mapping Theorem"
author: "Attila Csordas"
---
In the tough journey of this research project, the strategy for the proof has evolved. The current, robust version of the proof relies on an algebraic refutation of a forced recurrence relation. However, an earlier version was built on a different, more purely analytical contradiction engine.

The core of that earlier strategy is the powerful theorem presented below: the **Line-to-Line Mapping Theorem**. While this theorem and its proof are standard results in complex analysis, their application in the broader context of my RH proof contained a subtle but critical flaw.

As an exercise for the reader, I am presenting the theorem and its proof here. The challenge is to find the error in how this otherwise correct theorem was applied in the now-superseded proof strategy. I will discuss the flaw in detail in a subsequent post. For now, let's examine the engine itself using the wording from the earlier manuscript.

---

### The Core Analytical Engine

The proof presented in this paper establishes the Riemann Hypothesis by demonstrating, through a *reductio ad absurdum*, that the assumption of a hypothetical off-critical zero leads to a fundamental contradiction. The logical architecture is built around a single, powerful analytical engine whose components are applied in different ways to refute all possible cases.

1.  **The Core Analytical Engine:** The proof's mechanism is the combination of two results.
    * First, we establish that for any entire function $H(s)$ satisfying the Functional Equation (FE) and Reality Condition (RC), its derivative $H'(s)$ must be purely imaginary on the critical line (the Imaginary Derivative Condition, IDC).
    * Second, we use the Line-to-Line Mapping Theorem, which states that any entire function mapping a line to another line must be an affine polynomial.

This engine translates the global symmetries of $H(s)$ into a fatal local constraint on the structure of its derivative, $H'(s)$.
 
We conclude our general setup with a formal proof of a theorem that is a linchpin of our main argument. This theorem constrains the structure of any entire function whose range is restricted to a line. The constraint it provides will ultimately prove fatal to the hypothesis of an off-critical zero.

> ### Theorem (Line-to-Line Mapping for Entire Functions)
> *If an entire function $f(z)$ maps a line $L_1$ into a line $L_2$, then $f(z)$ must be an affine transformation ($f(z) = \alpha z + \beta$) or a constant.*

---

### Proof

The proof proceeds by demonstrating that the theorem's validity is independent of the specific orientation or position of the lines $L_1$ and $L_2$. We achieve this by showing that any arbitrary line-to-line mapping problem can be rigorously transformed into the algebraically simplest case---a polynomial with real coefficients mapping the real axis to itself---without any loss of generality. The conclusion derived from this simplified case then applies to the original problem through the same invertible transformations. This standard geometric technique allows us to analyze the intrinsic properties of the function, which are invariant under rotation and translation of the coordinate system.

The proof is divided into two exhaustive cases.

#### Case 1: $f(z)$ is constant.

The theorem statement allows for $f(z)$ to be constant. This specific case occurs if the entire function $f(z)$ maps all points on the line $L_1$ to a single point, which we will call $c$. By definition, this point $c$ must be on the line $L_2$.

To formalize this using the principles of analytic continuation, we introduce a second "helper" function for comparison. Let **$g(z)$** be the constant function defined as $g(z) = c$ for all $s \in \mathbb{C}$. As a constant function, $g(z)$ is trivially an entire function.

We now have two entire functions, $f(z)$ and $g(z)$, and can compare their values:
* For every point $z \in L_1$, our premise for this case is that $f(z) = c$.
* For every point $z \in L_1$, by definition, we also have $g(z) = c$.

Therefore, we have established that $f(z) = g(z)$ on the infinite set of points constituting the line $L_1$. The Identity Theorem states that if two entire functions agree on a set of points that has a limit point, they must be identical everywhere. Since a line contains limit points, the conditions of the theorem are met.

Thus, we must have $f(z) = g(z)$ for all $z \in \mathbb{C}$. Since $g(z)$ is the constant function $c$, we conclude that $f(z)$ must also be the constant function $c$.

#### Case 2: $f(z)$ is non-constant.

The proof for this case proceeds in two parts. First, we establish that $f(z)$ must be a polynomial. Second, we prove that this polynomial must have a degree of at most 1.

##### Part A: The Entire Function Must Be a Polynomial

Let $f(z)$ be a non-constant entire function that maps the line $L_1$ to a subset of the line $L_2$.

1.  **Omitted Values:** Since the range of the function $f(z)$ is contained within the line $L_2$, the function necessarily omits all values in the complex plane $\mathbb{C}$ that do not lie on the line $L_2$. This set of omitted values is infinite.

2.  **Invoking Picard's Great Theorem:** A fundamental result concerning transcendental entire functions is Picard's Great Theorem. A direct consequence of the theorem is:

    > **Picard's Theorem (Value-Attaining Property):** A transcendental entire function attains every complex value, with at most one possible exception, infinitely many times.

3.  **Conclusion of Part A:** Our function $f(z)$ is shown to omit an infinite number of values from its range. This is in direct contradiction to Picard's Theorem, which states that it can omit at most one. Therefore, the function $f(z)$ cannot be a transcendental entire function. As an entire function must be either transcendental or a polynomial, we conclude that $f(z)$ must be a polynomial. Let us call it $P(z)$.

##### Part B: The Polynomial Must Have Degree at Most 1

We now have a non-constant polynomial $P(z)$ of some degree $N \ge 1$ that maps the line $L_1$ into the line $L_2$. The proof proceeds by showing that the assumption $N \ge 2$ leads to a contradiction.

1.  **Simplifying the Geometry to a Real-Valued Polynomial:**
    Our goal is to transform the general problem into a simpler, equivalent problem of a polynomial with real coefficients mapping the real axis to itself. This is achieved in two stages using invertible affine maps. An affine map $M(z) = az+b$ is invertible if $a \neq 0$.

    **Stage 1: Mapping the Domain to the Real Axis.**
    First, we map the domain line $L_1$ to the real axis $\mathbb{R}$. Let $M_1(z) = a z + b$ be an invertible affine map that maps $L_1$ onto $\mathbb{R}$. We then define a new polynomial by composing $P(z)$ with the inverse map $M_1^{-1}(z)$:
    $$
    Q(z) := P(M_1^{-1}(z))
    $$
    This new polynomial $Q(z)$ now maps the real axis $\mathbb{R}$ into the line $L_2$. The degree of $Q(z)$ is the same as the degree of $P(z)$, which is $N$.

    **Stage 2: Rotating the Image to the Real Axis.**
    Next, we transform the polynomial $Q(z)$ into a new polynomial $S(z)$ that maps the real axis to the real axis. We know that for any real input $x$, the output $Q(x)$ must lie on the line $L_2$. Any line $L_2$ can be parameterized as $z_0 + \lambda \cdot e^{i\theta}$ for some fixed point $z_0 \in L_2$ and angle $\theta$. Thus, for any real $x$, there exists a real $\lambda$ such that:
    $$
    Q(x) = z_0 + \lambda e^{i\theta}
    $$
    We define a new function $S(z)$ which effectively "back-rotates" the output to the real axis:
    $$
    S(z) := e^{-i\theta} (Q(z) - z_0)
    $$
    For any real input $x$, $S(x) = e^{-i\theta}((z_0 + \lambda e^{i\theta}) - z_0) = \lambda$, which is a real number. Since $S(z)$ is a polynomial that is real on the real axis, it must have exclusively real coefficients. Its degree is also preserved as $N$.

2.  **Topological Constraint on the Image of $S(z)$:**
    We have constructed a polynomial $S(z)$ of degree $N$ with real coefficients, which maps the real axis to the real axis. Since $S(z)$ is a continuous open map, the image of the upper half-plane, $S(\mathbb{H})$, is an open, connected set. The boundary of this image, $\partial(S(\mathbb{H}))$, is contained within the image of the boundary, $S(\mathbb{R})$, which is a subset of the real axis. An open, connected set in $\mathbb{C}$ whose boundary is entirely on the real line must lie entirely in either the upper half-plane or the lower half-plane.

3.  **Argument by Asymptotic Contradiction:**
    We now show that this confinement to a single half-plane is incompatible with the behavior of $S(z)$ if its degree $N \ge 2$. For complex numbers $z$ with a very large modulus, $S(z) \approx a_N z^N$, where $a_N$ is the real leading coefficient.

    Let's trace the image of a large semi-circular path in the upper half-plane: $z(\lambda) = R e^{i\lambda}$ for $\lambda \in [0, \pi]$.
    The image is approximately:
    $$
    S(z(\lambda)) \approx a_N (R e^{i\lambda})^N = a_N R^N e^{iN\lambda}
    $$
    The argument (angle) of this image point is approximately $\arg(a_N) + N\lambda$. As the input angle $\lambda$ sweeps from $0$ to $\pi$, the output angle sweeps a total range of $N\pi$ radians.

    If we assume $N \ge 2$, the total angular sweep is at least $2\pi$ radians ($360^\circ$). This means the image path must point in all directions, including into both the upper and lower half-planes. This directly contradicts our finding from the topological step, which proved that the image must be confined to a single half-plane.

    Therefore, the degree of the polynomial $S(z)$ cannot be $N \ge 2$.

4.  **Conclusion of Part B:**
    We have refuted $N \ge 2$. Since we are in the non-constant case ($N \ge 1$), the only remaining possibility is $N=1$. The polynomial $S(z)$ must be of degree 1. As $S(z)$ was constructed from the original entire function $f(z)$ using only invertible affine transformations, it follows that $f(z)$ must also be an affine transformation.

This completes the proof.
