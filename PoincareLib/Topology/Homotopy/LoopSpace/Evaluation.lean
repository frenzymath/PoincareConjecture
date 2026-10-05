import PoincareLib.Topology.Homotopy.LoopSpace.Basic

/-!
# Evaluation and constant loops in the C1 topology

The last step of Morgan--Tian Lemma 18.27, printed p. 434, uses the
continuous inclusion of the manifold as constant loops. Here continuity is
checked for the exact induced topology in the frozen loop-space contract.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareMT.LoopSpace

/-- Compactness of the contract's circle subtype, used for joint evaluation
in the compact-open C1 topology of MT Lemma 18.27, p. 434. -/
instance loopCircleCompactSpace : CompactSpace LoopCircle := by
  let e : (Metric.sphere (0 : LoopPlane) 1) ≃ₜ LoopCircle :=
    Homeomorph.setCongr (by ext z; exact mem_sphere_zero_iff_norm)
  exact e.compactSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- The value component of the C1 topology, used in MT Lemma 18.27, p. 434. -/
def loopValues : C(C1FreeLoopSpace (M := M), C(LoopCircle, M)) :=
  ⟨fun γ => ⟨γ.toFun, γ.continuous⟩, by
    have h : Continuous (fun γ : C1FreeLoopSpace (M := M) =>
        ((⟨γ.toFun, γ.continuous⟩ : C(LoopCircle, M)), c1LoopTangent γ)) :=
      continuous_induced_dom
    exact h.fst⟩

/-- The tangent component of the C1 topology of MT p. 429. -/
noncomputable def loopTangents :
    C(C1FreeLoopSpace (M := M), C(LoopCircle, TangentBundle (𝓡 3) M)) :=
  ⟨c1LoopTangent, by
    have h : Continuous (fun γ : C1FreeLoopSpace (M := M) =>
        ((⟨γ.toFun, γ.continuous⟩ : C(LoopCircle, M)), c1LoopTangent γ)) :=
      continuous_induced_dom
    exact h.snd⟩

/-- Joint value evaluation is continuous in the intrinsic C1 topology.
Source: the family contraction in MT Lemma 18.27, printed p. 434. -/
theorem continuous_loop_eval :
    Continuous (fun p : C1FreeLoopSpace (M := M) × LoopCircle => p.1 p.2) :=
  continuous_eval.comp ((loopValues (M := M)).continuous.prodMap continuous_id)

/-- Joint tangent evaluation is continuous in the intrinsic C1 topology.
Source: the family contraction in MT Lemma 18.27, printed p. 434. -/
theorem continuous_loop_tangent_eval :
    Continuous (fun p : C1FreeLoopSpace (M := M) × LoopCircle =>
      c1LoopTangent p.1 p.2) :=
  continuous_eval.comp ((loopTangents (M := M)).continuous.prodMap continuous_id)

/-- The contract's C1 continuity criterion retains both compact-open
components, as required in MT Lemma 18.27, p. 434. -/
theorem continuous_iff_values_tangents {X : Type v} [TopologicalSpace X]
    (f : X → C1FreeLoopSpace (M := M)) :
    Continuous f ↔ Continuous (fun x => loopValues (f x)) ∧
      Continuous (fun x => loopTangents (f x)) := by
  exact continuous_induced_rng.trans continuous_prodMk

/-- Evaluation at a fixed circle point is continuous; this is the map
`f(c) = Gamma(c)(x_0)` in MT Lemma 18.27, p. 434. -/
def loopEvaluation (z : LoopCircle) : C(C1FreeLoopSpace (M := M), M) :=
  ⟨fun γ => γ z, (continuous_eval_const z).comp (loopValues (M := M)).continuous⟩

/-- The intrinsic derivative of a constant loop is the zero tangent vector.
This verifies the constant-loop inclusion used in MT Lemma 18.27, p. 434. -/
theorem c1LoopTangent_constant (x : M) :
    c1LoopTangent (constantC1Loop x) =
      ContinuousMap.const LoopCircle (⟨x, 0⟩ : TangentBundle (𝓡 3) M) := by
  apply ContinuousMap.ext
  intro z
  dsimp only [c1LoopTangent, constantC1Loop]
  simp only [mfderiv_const]
  rfl

/-- The inclusion as constant C1 loops is continuous, including its tangent
component. Source: MT Lemma 18.27, printed p. 434. -/
theorem continuous_constantC1Loop :
    Continuous (constantC1Loop : M → C1FreeLoopSpace (M := M)) := by
  apply (continuous_iff_values_tangents _).mpr
  constructor
  · change Continuous (ContinuousMap.const LoopCircle : M → C(LoopCircle, M))
    exact ContinuousMap.continuous_const'
  · change Continuous (fun x : M => c1LoopTangent (constantC1Loop x))
    simp_rw [c1LoopTangent_constant]
    exact ContinuousMap.continuous_const'.comp
      (Bundle.Trivialization.continuous_zeroSection ℝ)

/-- The continuous constant-loop inclusion in MT Lemma 18.27, p. 434. -/
noncomputable def constantLoopMap : C(M, C1FreeLoopSpace (M := M)) :=
  ⟨constantC1Loop, continuous_constantC1Loop⟩

end PoincareMT.LoopSpace
