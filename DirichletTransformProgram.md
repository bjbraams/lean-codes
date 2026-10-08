# The general Dirichlet transform — research programme

Started 5 October 2026. This document tracks the programme of developing the general regularized
Dirichlet transform `G ↦ F`, of which Carlson's Dirichlet averaging `f ↦ F` is the special case
`G(u, z) = f(u · z)`.

## Setting

For a kernel `g` on the standard simplex `Δ ⊂ ℝ^ι`, the regularized transform is

`T_b[g] = ∫_Δ ∏ᵢ uᵢ^(bᵢ - 1) / Γ(bᵢ) · g(u) du`,

defined natively for `Re bᵢ > 0` (`Dirichlet.regDirichletIntegral`) and continued to an entire
function of `b` for kernels smooth near `Δ` (`Dirichlet.IsRegDirichletContinuation`,
`Dirichlet.exists_isRegDirichletContinuation`). The family `Pᵦ = ∏ uᵢ^(bᵢ-1)/Γ(bᵢ)` is an entire
family of distributions supported on `Δ`; `T_b[g] = ⟨Pᵦ, g⟩`.

Two directions of continuation must be distinguished:

* **in the parameters `b`**: the kernel is fixed and smooth; this is essentially complete;
* **in the kernel's domain**: the kernel is holomorphic on a complex domain that does not
  contain the real simplex (for Carlson's kernels: nodes outside a convex domain). This is the
  content of Carlson (1969), Theorem 8, whose simply connected case is proved
  (`Dirichlet.Average.SimplyConnected`).

## Plan

### Step 1. Complete the parameter theory (done)

1. **Face formula at a zero parameter.** If `bᵢ = 0`, then `T_b[g]` is the transform, on the
   face `uᵢ = 0`, of the restriction of `g`, with the remaining parameters.
2. **Integration by parts for all parameters.** For a tangential derivative `∂ⱼᵢ` (moving mass
   from `i` to `j`): `T_b[∂ⱼᵢ g] = T_{b - eᵢ}[g] - T_{b - eⱼ}[g]`, as an identity of entire
   functions.
3. **Face formula at `bᵢ = -m`.** From 1 and 2: with any `j ≠ i`,
   `T_b[g] = ∑ₖ C(m, k) T^face_{b' - (m - k) eⱼ}[(∂ⱼᵢ^k g)|face]`. This contains Carlson's
   omission of a vanishing parameter as the case `m = 0`.
4. **Uniqueness.** A continuous kernel whose transform vanishes identically vanishes on `Δ`
   (moments of `g` are values of `T` at shifted parameters).
5. **Continuity.** On each compact set of parameters, `|T_b[g]|` is bounded by a constant times
   a `Cᴺ` norm of `g` near `Δ`. This makes termwise and limiting arguments routine.

Status of step 1 (5 October 2026):

| Item | Lean | Module |
| --- | --- | --- |
| 1 | `IsRegDirichletContinuation.face_zero` | `SimplexMellin.Face` |
| 2 | `IsRegDirichletContinuation.tangent` (existing); `regDirichletTransform_tangentDeriv` | `Laws`, `Face` |
| 3 | `regDirichletTransform_sub_single_eq_sum`, `regDirichletTransform_eq_sum_face` | `Face` |
| 4 | `IsRegDirichletContinuation.eqOn_of_eq_natCast_add_one`, `eqOn_of_regDirichletTransform_eq` | `SimplexMellin.Uniqueness` |
| 5 | qualitative form exists: `exists_entire_joint_regDirichletContinuation_kernel` (joint holomorphy in auxiliary parameters), `Dirichlet.Transform.Series` (locally uniform limits) | `Parametric`, `Series` |

The quantitative `Cᴺ` estimate of item 5 is done (`SimplexMellin.Estimate`,
2026-10-06): on a compact set `K ⊆ {-N < Re bᵢ}`, every continuation satisfies `‖T_b[g]‖ ≤ C_K A`
when the derivatives of `g` of order at most `(card ι - 1) N` are bounded by `A` on the simplex
(`exists_norm_regDirichletContinuation_le`), and the entire transform satisfies the same on every
compact set (`exists_norm_regDirichletTransform_le`). The proof bounds the explicit continuation
formula, now a named definition `regDirichletShiftFormula` in `Dirichlet.Transform` (with
`regDirichletShiftFormula_spec`; the shifted integrals it uses are no longer private). Uniqueness needs only the values at the positive
integer parameters `m + 1` (the monomial moments, by `StdSimplexMeasure.MomentDetermination`).

### Step 2. Stick-breaking representation (done)

Represent `T_b[g]` for an arbitrary smooth kernel as an iterated regularized Euler integral of
`g ∘ σ`, where `σ : [0,1]^(k-1) → Δ` is the stick-breaking map. The measure identity
`Dirichlet.dirichletMeasure_eq_map_mergeMap` is one step of this; the regularized form carries
Gamma factors of partial sums, which must be handled as in the Theorem 8 proof.

Realized as the merging identity, one merge at a time (`Dirichlet.Transform.Merge`):

`Γ(b a + b a')⁻¹ T_b[g] = T₂_(b a, b a')[v ↦ T_(merged b)[y ↦ g (mergeMap v y)]]` for all `b`.

| Statement | Lean |
| --- | --- |
| Native identity, continuous kernel, positive parameters | `regDirichletIntegral_ofReal_eq_merge` |
| Identity of entire functions, given a jointly holomorphic inner continuation | `IsRegDirichletContinuation.inv_Gamma_mul_eq_merge` |
| Same, off the Gamma poles of `b a + b a'`, without the reciprocal | `IsRegDirichletContinuation.eq_Gamma_mul_merge` |
| Inner and outer continuations exist for kernels holomorphic near `Δ` | `exists_merge_continuation` |

The kernel-independent merging of Dirichlet measures moved from `Dirichlet.Average.Merge` to
`Dirichlet.Merge` (names unchanged; `mergeMap` is now defined over any ring of scalars so that
it complexifies). Carlson's merged averages are now a specialization.

Design decisions:

* The full stick-breaking map is the iteration of single merges; it is used by induction on the
  number of coordinates (as in the Theorem 8 proof) rather than stated for `[0,1]^(k-1)`.
  The two-coordinate transform is a regularized Euler integral (`regDirichletIntegral_fin_two`).
* At the level of entire functions the identity needs holomorphic dependence of the inner
  transform on the proportions `v`. For merely smooth kernels this would need smooth (not
  holomorphic) parameter dependence of the continuation, which the library does not have; the
  holomorphic case is what steps 3 and 4 use. The native identity holds for continuous kernels.

### Step 3. One-dimensional continuation along paths (simply connected case done)

For an Euler integral `∫₀¹ t^(a-1) (1-t)^(b-1) K_p(t) dt` whose kernel `K_p` is holomorphic on a
domain `Ω_p ∋ 0, 1` depending on parameters `p`: continuation along paths in `p` as long as
`0` and `1` remain in one simply connected component of `Ω_p`, by local deformation (the
endpoint-deformation lemma), gluing, and a monodromy argument. This is the research-level step.

Done for simply connected fibres (`Dirichlet.Average.FibreContinuation`):

| Statement | Lean |
| --- | --- |
| Two-node continuation from a given convex chart (refactor of the Theorem 8 two-node step) | `exists_twoNode_continuation_of_chart` |
| Relatively compact chart pieces containing two given points | `IsConvexChart.exists_restrict` |
| Two-node continuation over a domain `𝒲 ⊆ ℂ × P` with simply connected fibres | `exists_twoNode_continuation_of_fibres` |
| Euler integral with endpoints `0, 1` over simply connected fibres | `exists_regEulerIntegral_continuation_of_fibres` |

The continuation is holomorphic on the whole open set where both endpoints lie in the fibre, so
along any path of parameters keeping the endpoints in the (moving, simply connected) fibre. The
proof needs no monodromy argument: each fibre's Riemann chart gives the value, and holomorphy
in `p` comes from comparison with a chart piece of one fibre that lies in all nearby fibres.

Open: fibres that are not simply connected (Carlson's multiply connected case of Theorem 8),
where the continuation is multivalued. *Feasibility (assessed 2026-10-06):* not feasible with the
present infrastructure; see the note at the end of step 4. The tool is TauCeti's continuation along paths and
monodromy theorem (`TauCeti.Analysis.Complex.Conformal.Monodromy`, `GlobalBranch`), which is
one-dimensional: the natural formulation fixes all but one node and continues in that node.
For step 4 the simply connected case suffices for the planned applications: by the
characterization of ℂ-convex domains, a domain in `ℂⁿ` whose intersections with complex lines are
connected and simply connected gives simply connected fibres for vector nodes.

### Step 4. Fibrewise deformation theorem (done for Dirichlet averages)

Combine 2 and 3: if `g ∘ σ` extends holomorphically to a domain whose successive fibres satisfy
the hypotheses of step 3, then `T` continues in the kernel's parameters. Check: Carlson's
Theorem 8 (simply connected case) should follow. Then explore several-variable kernels
`h(u · Z)` (Carlson's double averages) on non-convex domains.

Done for Carlson-type kernels `g(u) = h(∑ uᵢ Zᵢ)` with `h` holomorphic on `D ⊆ ℂⁿ` and vector
nodes `Zᵢ ∈ ℂⁿ` (`Dirichlet.Average.SeveralVariables`):

| Statement | Lean |
| --- | --- |
| Hypothesis: complex-line sections of `D` through two of its points are simply connected | `HasSimplyConnectedLineSections` |
| Merging identity for vector nodes | `regVecDirichletAverage_ofReal_eq_merge` |
| Induction step: merged continuation ⟹ continuation | `exists_isJointRegVecContinuationOn_merge` |
| **Continuation to all nodes in `D`**, entire in the parameters | `exists_isJointRegVecContinuationOn` |
| Convex domains satisfy the hypothesis | `Convex.hasSimplyConnectedLineSections` |
| Planar simply connected domains satisfy it | `IsSimplyConnected.hasSimplyConnectedLineSections` |
| Theorem 8 (simply connected case) recovered for `n = 1` | `exists_isJointRegCarlsonContinuationOn_of_isSimplyConnected_of_lineSections` |

The successive fibres of the stick-breaking are the complex-line sections through the two
merged nodes; the merged node moves on that line, and the step-3 theorem continues the outer
Euler integral over the moving section. The Gamma factor of the merged parameter is removed as
in the planar proof (`Dirichlet.GammaPoles`).

Remarks and possible continuations:

* For open sets the hypothesis is `ℂ`-convexity (every intersection with a complex line is
  connected and simply connected), since a complex line meeting an open set meets it in at
  least two points. A formal definition of `ℂ`-convexity and the comparison with linear
  convexity are not attempted.
* Several-variable kernels are covered through the affine substitution `u ↦ ∑ uᵢ Zᵢ`. Kernels
  depending on `u` in other holomorphic ways (general `G(u, z)`) would need the merging
  identity's inner continuation to depend holomorphically on the proportions, which holds for
  holomorphic kernels (`exists_merge_continuation`), together with a fibre condition adapted
  to the kernel; this general form is not stated.
* Multiply connected fibres (monodromy) remain open, by decision of the maintainer.

**Multiply connected case: feasibility assessment (2026-10-06).** The natural formal statement
fixes all nodes but one and asserts, in TauCeti's sense (`TauCeti.ContinuesAlong`), that the germ
of the average in the free node continues along every path in `D`. The simply connected method
does not extend. It glues continuations defined on planar simply connected domains `U ⊆ D`
containing the nodes, and the germ reached along a path corresponds to a homotopy class of
contours from the fixed node to the moving one. A chain of planar simply connected domains can
realize only classes containing an embedded arc, and in `ℂ ∖ {p, q}` there are classes without
one (commutator classes). A proof therefore needs one of the following:

1. Euler integrals `∫_σ (w − y)^(a−1) (x − w)^(c−1) f(w) dw` over arbitrary contours `σ` in `D`,
   with branches continued along `σ`, singular endpoints, and invariance under homotopies that
   move the endpoints. `ToMathlib.Analysis.Integral.EndpointDeformation` covers only convex
   domains.
2. Averages on immersed simply connected domains (Riemann surfaces over `D`), which the affine
   formula `f(∑ uᵢ zᵢ)` does not see directly.

Either is a project of its own, much larger than steps 3–4. The rest of the TauCeti side is in
place (continuation along paths, concatenation, the monodromy theorem); the missing piece is the
contour-integral theory of item 1.

### Step 5. The Mellin bridge (done)

**Aim.** Identify the regularized Dirichlet transform as the angular part of the `k`-variable
Mellin transform in simplicial polar coordinates `x = r u` (`r = ∑ xᵢ`, `u ∈ Δ`), and use
Mellin–Fourier inversion to invert it. For a radial profile `φ` and a kernel `g` on `Δ`,

`∫_{ℝ₊ᵏ} x^(b−1) φ(∑ xᵢ) g(x / ∑ xᵢ) dx = ℳ[φ](b₁ + … + b_k) · ∏ᵢ Γ(bᵢ) · T_b[g]`,

and for `φ(r) = e^(−r)` the factor `ℳ[φ](B)` is `Γ(B)`. The probabilistic form of the same
identity (Gamma normalization gives the Dirichlet law) is `Dirichlet.Gamma`; the measure-level
polar decomposition is `MeasureTheory.lintegral_eq_radial_stdSimplex` (`StdSimplexMeasure.Radial`).

**Items.**

1. **Bochner polar decomposition.** Upgrade `lintegral_eq_radial_stdSimplex` to integrable
   complex-valued functions on the orthant:
   `∫_{ℝ₊ᵏ} G = ∫₀^∞ r^(k−1) ∫_Δ G(r u) du dr`, with the integrability transfer between the two
   sides. Mechanical; the nonnegative version carries the measure theory.
   *Done* (`StdSimplexMeasure.Radial`): `map_polarMap` (Lebesgue measure on the closed orthant
   is the image of `t^(k−1) dt ⊗ du` under `(t, u) ↦ t • u`), `integrable_comp_polarMap_iff`,
   and `integral_eq_radial_stdSimplex` for Banach-space-valued integrable functions.
2. **The `k`-variable Mellin transform.** Define `mvMellin G b = ∫_{ℝ₊ᵏ} x^(b−1) G(x) dx`
   (the name follows `mvBeta`), its convergence predicate, and the change of variables
   `x = exp y` identifying it with the Fourier transform of `y ↦ e^(⟨c, y⟩) G(exp y)` on a
   vertical plane `Re b = c`. Generic; candidate for `ToMathlib/Analysis` as a multivariable
   companion of Mathlib's `mellin`.
   *Done* (`ToMathlib/Analysis/MvMellinTransform.lean`): `mvMellin`, `MvMellinConvergent`,
   `mvMellin_eq_integral_exp` and `mvMellinConvergent_iff_integrable_exp` (substitution
   `x = exp y` with Jacobian `∏ exp yᵢ`), `mvMellin_eq_fourier` (Fourier form on
   `EuclideanSpace ℝ ι` at `−Im s / 2π`), `mvMellin_prod` (separable functions) and
   `mvMellin_exp_neg_sum` (`∏ Γ(sᵢ)`).
3. **The bridge.** For `g` continuous on `Δ`, `φ` with `MellinConvergent φ (Re B)` and
   `Re bᵢ > 0`: the displayed identity, with `T_b[g] = regDirichletIntegral b g`. Corollary for
   `φ = e^(−r)`: `mvMellin (x ↦ e^(−|x|) g(x/|x|)) b = Γ(B) ∏ Γ(bᵢ) T_b[g]`. For `k = 2` this
   relates to Mathlib's `mellin` and the beta integral; a sanity check, not a separate item.
   *Done* (`SimplexMellin.Bridge`): `mvMellin_radial_mul_eq` (for `φ` continuous on
   `(0, ∞)`, `g` continuous on `Δ`, `Re bᵢ > 0`) and `mvMellin_exp_neg_mul_eq`. No
   integrability hypothesis is needed: the proof uses the polar measure identity,
   `integral_map` (which needs only a.e. strong measurability), an a.e. factorization, and
   `integral_prod_mul`, so the two Bochner integrals agree in all cases.
4. **Continued form.** For smooth `g` the left side continues meromorphically in `b`, and the
   identity holds with the entire `regDirichletTransform`: the regularized transform is the
   Mellin transform with the Gamma poles of `Γ(B) ∏ Γ(bᵢ)` divided out. State it as an identity
   of meromorphic functions or, avoiding meromorphy, on the region where the Gamma factors are
   finite. Optional.
   *Done* (`SimplexMellin.Bridge`): `mvMellin_radial_eq_prod_Gamma_mul` (for smooth `g` and
   `φ` with entire Mellin transform, e.g. `differentiable_mellin_of_support_subset_Icc`) and
   `mvMellin_exp_neg_eq_Gamma_mul`: the multivariable Mellin transform is `∏ Γ(bᵢ)` (times
   `Γ(∑ b)` for `e^{−t}`) times an entire function built from `regDirichletTransform`.
5. **Inversion.** Recover `g` from `b ↦ T_b[g]` on a vertical plane `Re b = c` (all `cᵢ > 0`):
   apply Fourier inversion (Mathlib: `Continuous.fourierInv_fourier_eq`) to the exponential
   change of variables of item 2, then restrict the homogeneous extension to `Δ`. Hypotheses:
   continuity of `g` on the open simplex and integrability of `b ↦ Γ(B) ∏ Γ(bᵢ) T_b[g]` on the
   plane. The Gamma factor `Γ(B)` decays only in the direction `Im B`, so the integrability
   hypothesis is a smoothness condition on `g` in logarithmic coordinates near the faces; find
   a usable sufficient condition (for example, `g` smooth on a neighbourhood of `Δ` and
   compactly supported in the open simplex) and keep the general statement with the
   integrability hypothesis.
   *Done* (`SimplexMellin.Inversion`): `regDirichletIntegral_inversion`: for `g`
   continuous on `Δ`, `cᵢ > 0`, `b = c − 2πiξ` (`mellinPlane c ξ`), if
   `ξ ↦ Γ(∑ b) ∏ Γ(bᵢ) T_b[g]` (`simplexMellin`) is integrable on `ℝ^ι`, then at every interior
   point `g u = e ∫ (∏ uᵢ^(−bᵢ)) Γ(∑ b) ∏ Γ(bᵢ) T_b[g] dξ`. It uses Mathlib's pointwise Fourier
   inversion (`Integrable.fourierInv_fourier_eq`); integrability of the function being inverted
   follows from the new convergence lemma `mvMellinConvergent_radial_mul`.
   *Sufficient condition, done in a modified form:* the inversion is proved for any radial profile
   `φ` (`regDirichletIntegral_inversion_radial`, factor `φ(1)⁻¹`, with `ℳ[φ](∑ b)` in place of
   `Γ(∑ b)`), the `e^(−t)` version being the corollary `regDirichletIntegral_inversion`. For `φ`
   smooth with compact support in `(0, ∞)` and `g` smooth and vanishing at the points of the
   simplex with a coordinate below some `δ > 0`, the function in logarithmic coordinates is smooth
   with compact support (`contDiff_radialLog`, `hasCompactSupport_radialLog`), so its Fourier
   transform is integrable (TauCeti) and the integrability hypothesis holds
   (`integrable_simplexMellinRadial`). This gives the unconditional inversion formula
   `regDirichletIntegral_inversion_of_contDiff`. No Schwartz bounds are needed.
   *Exponential profile, done* (`SimplexMellin.Schwartz`): for smooth `g` vanishing
   near the faces the function in logarithmic coordinates is `G · A`, with
   `A(y) = exp(∑ (cᵢyᵢ − e^{yᵢ}))` Schwartz (`ToMathlib.Analysis.SchwartzExpExp`, by Faà di
   Bruno bounds) and `G(y) = g(e^y / ∑ e^y)` of temperate growth (it equals a compactly supported
   smooth function composed with the linear map `y ↦ y − y_{i₀} 𝟙`). Hence
   `integrable_simplexMellin` and the unconditional `regDirichletIntegral_inversion_exp_of_contDiff`.
6. **Plancherel.** An `L²` isometry between `g` on `Δ` (weighted by `u^(2c−1)`) and
   `Γ(B) ∏ Γ(bᵢ) T_b[g]` on the plane, if Mathlib's `L²` Fourier theory suffices; otherwise
   record as open.
   *Done* (`integral_norm_sq_simplexMellinRadial`): for a smooth profile with compact support in
   `(0, ∞)` and a smooth kernel vanishing near the faces,
   `∫ |ℳ[φ](∑ b) ∏ Γ(bᵢ) T_b[g]|² dξ = ℳ[|φ|²](2∑c) ∏ Γ(2cᵢ) T_{2c}[|g|²]`, from Mathlib's
   Plancherel theorem for Schwartz functions and the bridge at `2c`.

**Consequences and later steps.** Item 5 makes the uniqueness theorem of step 1.4
constructive. Items 5–6 prepare a Paley–Wiener description of the image (which entire functions
are transforms of smooth kernels, with the growth estimate deferred in step 1.5) and the
interpolation of moments (Fritz Carlson's theorem on entire functions of exponential type). The
Euler–Mellin (A-hypergeometric) and symmetric-cone directions build on the bridge but are not
part of step 5.

**Placement (decided 5 October 2026).** The theory of the transform beyond what Carlson's
averages need has its own top-level library `SimplexMellin/`, parallel to `Dirichlet/` and
`Carlson/`: `SimplexMellin.Face`, `.Uniqueness`, `.Bridge`, `.Inversion` and `.Schwartz`.
The transform's definition, continuation, structural laws and merging identity stay in
`Dirichlet.Transform`, because `Dirichlet.Average` and `Carlson` build on them; `Dirichlet` is
the shared basis of the two collections. `SimplexMellin` and `Carlson` do not import each other,
and `Dirichlet` imports neither (`AGENTS.md`). Declarations keep the `Dirichlet` namespace.
Generic inputs stay in `ToMathlib.Analysis.MvMellinTransform`,
`ToMathlib.Analysis.SchwartzExpExp` and `StdSimplexMeasure.Radial`. Future work (Paley–Wiener,
the quantitative growth estimate, Euler–Mellin integrals, symmetric cones) goes to
`SimplexMellin`.

### Step 6. Paley–Wiener description of the image (done)

For `g` continuous on `Δ` and vanishing at the points with a coordinate below `δ > 0` (in
logarithmic coordinates `y = log u`, support in the box `log δ ≤ yᵢ ≤ 0`), consider the simplex
Mellin transform `S_g(b) = ∫_Δ u^(b−1) g(u) du = ∏ Γ(bᵢ) T_b[g]`.

**Necessity, done** (`SimplexMellin.PaleyWiener`):

| Property of `S_g` | Lean |
| --- | --- |
| `T_b[g]` (the native integral) is entire; `S_g = ∏ Γ(bᵢ) · T_b[g]` | `analyticOnNhd_regDirichletIntegral_of_vanish`, via the Pochhammer shift identity `regDirichletIntegral_eq_ascPochhammer_mul` |
| Sum-shift equation `S_g(b) = ∑ᵢ S_g(b + eᵢ)` | `IsRegDirichletContinuation.sum_shift` (regularized form, existing) |
| Exponential type: `|S_g(b)| ≤ ‖g‖₁ ∏ max(1, δ^(Re bᵢ − 1))` | `norm_integral_monomial_mul_le_of_vanish` |
| Schwartz on vertical planes after a radial factor `ℳ[φ](∑ b)`, `φ ∈ C_c^∞(0, ∞)` (smooth `g`) | `exists_schwartzMap_simplexMellinRadial` |

`S_g` alone does not decay rapidly in all imaginary directions: where all `Im bᵢ` have the same
sign the phase `⟨Im b, log u⟩` has a non-degenerate stationary point on `Δ`, giving decay
`|Im b|^(−(k−1)/2)` only. So the image is not a classical Paley–Wiener space in `b`; the radial
factor is part of the description.

**Paley–Wiener on hyperplanes, done** (`SimplexMellin.LogRatio`, `SimplexMellin.Hyperplane`).
The image is described cleanly on the hyperplanes `∑ bᵢ = s`. In log-ratio coordinates
`w j = log (u j / u i₀)` (Jacobian `∏ uᵢ`, `Z(w) = 1 + ∑ e^(w j)`),

`S_g(b) = ∫ e^(⟨b', w⟩) Z(w)^(−s) g(u(w)) dw`,   `b' = (b j)_(j ≠ i₀)`,

a Fourier–Laplace transform in `k − 1` variables of the compactly supported function
`Z^(−s) g(u(w))`. Hence (`exists_kernel_of_paleyWiener`): every entire `P(b')` such that
`ζ ↦ P(−2πiζ)` has Paley–Wiener bounds for a box `|w j| ≤ ρ j` is `S_g` on the hyperplane, for the
kernel `g = Z^s ψ(w(u))`, `ψ` the Paley–Wiener inverse, which is continuous on `Δ`, smooth near
`Δ` (it is scale-invariant and vanishes near the boundary), and vanishes where some
`uᵢ < (1 + ∑ e^(ρ j))⁻¹ e^(−∑ ρ j)`. Conversely, for smooth `g` vanishing where some `uᵢ < δ` the
function `Z^(−s) g(u(w))` is smooth and supported in the box `|w j| ≤ |log δ|`, so the
restriction has Paley–Wiener bounds; and by Fourier inversion the restriction to one hyperplane
determines a continuous kernel vanishing near the faces.

| Ingredient | Lean |
| --- | --- |
| Classical Paley–Wiener on `ℝⁿ` | `PaleyWiener.fourierInv_of_bound` (`ToMathlib.Analysis.Fourier.PaleyWiener`) |
| Change of variables to log-ratio coordinates | `integral_stdSimplex_eq_integral_logRatio` (via the bridge at `b = 𝟙`, a shear of exponential coordinates, and `∫ e^(kτ) e^(−Z e^τ) dτ = Z^(−k) Γ(k)`) |
| Hyperplane formula | `integral_monomial_mul_eq_integral_logRatio` |
| Laplace transforms of compactly supported functions are entire | `analyticOnNhd_integral_cexp_mul` |
| Identification at complex points | uniqueness from real points (`AnalyticOnNhd.eq_of_eqOn_posReal_pi`) |
| Sufficiency | `exists_kernel_of_paleyWiener` |
| Smoothness of the constructed kernel | `smoothNearStdSimplex_logRatioKernel` |
| Classical necessity on `ℝⁿ` (integration by parts) | `norm_fourierLaplace_le_of_contDiff` |
| Necessity on hyperplanes | `integral_hyperplane_eq_fourierLaplace`, `norm_integral_hyperplane_le` |
| Injectivity on one hyperplane | `eqOn_of_integral_hyperplane_eq` (via `eq_zero_of_fourierLaplace_eq_zero`) |

**Global description, done** (`SimplexMellin.Image`). The hyperplane results extend to all of `ℂ^ι` without a
radial factorization, using Carlson's theorem (step 7). Let `S` be entire with
(a) the sum-shift equation `S(b) = ∑ᵢ S(b + eᵢ)`,
(b) the bound `|S(b)| ≤ C ∏ max(1, δ^(Re bᵢ − 1))`, and
(c) Paley–Wiener bounds on one hyperplane `∑ b = s₀`.
Sufficiency on that hyperplane gives a kernel `g` with `S = S_g` there. The difference
`D = S − S_g` satisfies (a) and (b), so it vanishes on every hyperplane `∑ b = s₀ − n`, `n ∈ ℕ`.
On a line `z ↦ D(b − z 𝟙/k)` it is of exponential type in `Re z ≥ 0`, bounded on vertical lines
and zero at the integers; Carlson's theorem makes it vanish, hence `D = 0` on
`Re ∑ b ≤ Re s₀` and everywhere by the identity theorem. Necessity of (a)–(c) is proved above,
so (a)–(c) characterize the transforms `S_g` of smooth kernels vanishing near the faces.

| Statement | Lean |
| --- | --- |
| `S_g(b) = ∫_Δ u^(b−1) g` (native) | `simplexMoment` |
| `S_g` is entire (shift by `m`, `S_g(b) = ∏ Γ(bᵢ + m) T_(b+m)[g / (∏ u)^m]`) | `differentiable_simplexMoment`, `simplexMoment_eq_prod_Gamma_mul` |
| Sum-shift equation | `simplexMoment_eq_sum` |
| Global sufficiency | `exists_kernel_of_sum_shift` |
| Global necessity | `simplexMoment_necessity` |
| **Characterization** | `exists_kernel_iff` |

The hyperplane necessity theorem `norm_integral_hyperplane_le` now assumes only smoothness near
the simplex (`SmoothNearStdSimplex`), the class produced by the sufficiency construction.

The example `D(b) = sin(2π(∑ b − s₀)) S_{g₀}(b)` satisfies (a) and vanishes on the hyperplane
`∑ b = s₀`; it is excluded by (b) only, through its growth in `Im ∑ b`. So the bound on vertical
lines in (b) is essential, and no description by one hyperplane plus the sum-shift equation alone
is possible.

### Step 7. Carlson's theorem (F. Carlson, 1914; done)

**Statement.** Let `f` be holomorphic on `Re z ≥ 0` with `|f(z)| ≤ C e^(τ|z|)` there and
`|f(iy)| ≤ C e^(c|y|)` with `c < π`. If `f(n) = 0` for all `n ∈ ℕ`, then `f = 0`. The constant `π`
is sharp (`sin πz`).

**Proof plan (Phragmén–Lindelöf only).** Put `g = f / sin(πz)`, with the removable singularities
at `ℕ` filled in (`dslope`). Off the `1/4`-discs around the integers `|sin πz|` is bounded below,
and on the discs the maximum modulus principle applies, so `g` is of exponential type in the
half-plane; on the imaginary axis `|g(iy)| ≤ C' e^((c − π)|y|)`. Multiply by
`e^(−α(z+1) log(z+1))` with `0 < α ≤ 2(π − c)/π`: on the imaginary axis the factor grows at most like
`e^(απ|y|/2)`, so the product stays bounded, and on the positive real axis it decays
superexponentially. Mathlib's `PhragmenLindelof.eq_zero_on_right_half_plane_of_superexponential_decay`
then gives `g = 0`, hence `f = 0`.

**Uses.**

1. The global description of the image in step 6 (the main application).
2. Moments determine `S_g` on `Re b ≥ 1`: there `|S_g(b)| ≤ ‖g‖₁` for every integrable `g`, so
   Carlson's theorem in each variable shows that `S_g` is determined by its values at `b = n + 𝟙`,
   `n ∈ ℕ^ι`, the monomial moments. This is an analytic alternative to the moment determination
   of step 1.4. It applies to `S_g`, not to `T_b[g] = S_g / ∏ Γ(bᵢ)`, which is not of exponential
   type.
3. Canonical continuation of lattice data: a sequence `a_n` admits at most one continuation of
   exponential type with imaginary type below `π`. Existence is a separate question (Hausdorff
   moment conditions, Newton–Nörlund interpolation series).
4. A several-variable Ramanujan master theorem with simplex structure, through the Mellin bridge
   `ℳ[φ](∑ b) ∏ Γ(bᵢ) T_b[g]` of step 5. Exploratory.

**Placement.** `ToMathlib.Analysis.Complex.Carlson` (generic complex analysis, absent from Mathlib
and TauCeti); the applications go to `SimplexMellin`.

**Status.** The theorem is proved as planned (`Complex.eqOn_zero_of_natCast_eq_zero`), for `f`
differentiable at every point of the closed half-plane, and in several variables by induction on
the coordinates (`Complex.eqOn_zero_of_natCast_eq_zero_pi`).

* Use 1: done (`SimplexMellin.Image`).
* Use 2: done (`SimplexMellin.Lattice`, `simplexMoment_eqOn_of_moments_eq`): kernels continuous
  on the simplex with the same monomial moments have the same transform on `Re b > 0`, by
  Carlson's theorem on `Re b ≥ 1`, where `‖S_g‖ ≤ ‖g‖₁` (`norm_simplexMoment_le`), and the identity
  theorem.
* Use 3: done. Uniqueness: `Complex.eqOn_of_natCast_eq_pi`. Existence goes through the moment
  problem on the simplex (`StdSimplexMeasure.MomentProblem`, `exists_measure_iff`): a sequence on
  `ℕ^ι` is the moment sequence of a finite measure on the simplex iff it is nonnegative and
  satisfies the sum-shift equation. For two coordinates this is Hausdorff's moment problem. The
  proof expands `(∑ xᵢ)^K` in the monoid algebra of `ℕ^ι`, uses the falling-factorial identity
  for the discrete measures `∑_{|k|=N} multinomial(k) a(k) δ_{k/N}`, Stone–Weierstrass, and the
  Riesz–Markov–Kakutani theorem. The continuation of the shifted data `n ↦ a(n + 𝟙)` is
  `b ↦ ∫ u^(b+𝟙) dμ`, holomorphic on `Re b > −1` and bounded by `a(0)` on `Re b ≥ 0`
  (`SimplexMellin.Lattice`: `exists_continuation_of_satisfiesSumShift`,
  `eqOn_of_natCast_eq_of_bounded`). The shift is necessary: the point mass at a vertex gives
  data `1, 0, 0, …` in another coordinate, which have no continuation of Carlson's class.
* Use 4: done.
  * **One-variable master theorem, Hardy's form** (`ToMathlib.Analysis.SpecialFunctions.RamanujanMaster`,
    `Complex.ramanujan_master_theorem`). For `φ` holomorphic on `Re z > −δ` with
    `|φ(z)| ≤ C e^(P Re z + A|Im z|)`, `A < π`, the Mellin–Barnes integral `F` equals
    `∑ φ(k)(−x)^k` for `0 < x < e^(−P)`, and `∫₀^∞ x^(s−1) F(x) dx = π φ(−s)/sin πs` for
    `0 < Re s < δ`.
  * **The contour tools** (`ToMathlib.Analysis.MellinBarnes`), built instead of a residue theorem
    for rectangles:
    * Cauchy's theorem on vertical strips.
    * Crossing a simple pole changes a line integral by `2π·Res`. The proof subtracts a
      comparison function with explicitly computable line integrals.
    * `mellin_mellinInv_eq`, the reverse of Mathlib's Mellin inversion.
  * **Several-variable form with simplex structure** (`SimplexMellin.Master`). Through the
    bridge, `∫_{ℝ₊^ι} x^(b−1) F(∑x) g(x/∑x) dx = π/sin(π∑b) · φ(−∑b) · ∏Γ(bᵢ) · T_b[g]`, and
    `F(∑x) g(x/∑x) = ∑ φ(k)(−∑x)^k g(x/∑x)` near the origin.
  * **Open:** a master theorem for genuinely multivariable series `∑ c(n) ∏(−xᵢ)^{nᵢ}/nᵢ!`
    (the method of brackets) is not attempted.

## Status log

* 2026-10-05: programme set up; step 1 started.
* 2026-10-05: step 1 items 1–4 proved (`SimplexMellin.Face`, `SimplexMellin.Uniqueness`);
  item 5 covered qualitatively, quantitative estimate deferred. Next: step 2.
* 2026-10-05: step 2 done (`Dirichlet.Merge`, `Dirichlet.Transform.Merge`). Next: step 3.
* 2026-10-05: step 3 done for simply connected fibres (`Dirichlet.Average.FibreContinuation`);
  multiply connected fibres (monodromy) open. Next: step 4.
* 2026-10-05: step 4 done for averages of functions of several variables
  (`Dirichlet.Average.SeveralVariables`); Theorem 8 recovered. Multiply connected case left open
  by decision. Programme complete in its planned scope.
* 2026-10-05: step 5 (Mellin bridge) drafted; placement decision deferred.
* 2026-10-05: step 5 item 1 done (polar coordinates in `StdSimplexMeasure.Radial`).
* 2026-10-05: step 5 item 2 done (`ToMathlib.Analysis.MvMellinTransform`).
* 2026-10-05: step 5 item 3 done (the bridge, `SimplexMellin.Bridge`).
* 2026-10-05: step 5 item 5 done (inversion, with the integrability hypothesis); sufficient
  condition open.
* 2026-10-05: unconditional inversion for smooth kernels vanishing near the faces (compactly
  supported radial profile); the `e^(−t)`-profile integrability remains open.
* 2026-10-05: step 5 complete: continued form (item 4), Plancherel (item 6), and the
  exponential-profile integrability via Schwartz bounds.
* 2026-10-05: the transform theory moved to the new top-level library `SimplexMellin/`.
* 2026-10-05: step 6 (Paley–Wiener) started; necessity proved (`SimplexMellin.PaleyWiener`);
  sufficiency needs a classical Paley–Wiener theorem on `ℝⁿ` and a radial factorization.
* 2026-10-05: classical Paley–Wiener on `ℝⁿ` proved (`ToMathlib.Analysis.Fourier.PaleyWiener`).
* 2026-10-06: sufficiency on hyperplanes `∑ b = s` proved (`SimplexMellin.LogRatio`,
  `SimplexMellin.Hyperplane`).
* 2026-10-06: hyperplane Paley–Wiener completed: necessity bounds, injectivity on one
  hyperplane, and smoothness of the constructed kernel.
* 2026-10-06: step 7 (Carlson's theorem) added and proved
  (`ToMathlib.Analysis.Complex.Carlson`); with it the global Paley–Wiener description of the
  image (`SimplexMellin.Image`, `exists_kernel_iff`). Step 6 complete.
* 2026-10-06: step 1 item 5 (quantitative estimate) done (`SimplexMellin.Estimate`); step 7
  uses 2 and 3 (uniqueness) done (`SimplexMellin.Lattice`, several-variable Carlson). Feasibility
  of the remaining open items assessed: multiply connected case (step 3), existence for lattice
  data, master theorem (step 7).
* 2026-10-06: moment problem on the simplex solved (`StdSimplexMeasure.MomentProblem`); step 7
  use 3 complete (existence and uniqueness of continuations of lattice data).
* 2026-10-06: step 7 use 4: Ramanujan's master theorem (Hardy's form) with Mellin–Barnes contour
  tools in `ToMathlib`, and its simplex form (`SimplexMellin.Master`). Step 7 complete.
