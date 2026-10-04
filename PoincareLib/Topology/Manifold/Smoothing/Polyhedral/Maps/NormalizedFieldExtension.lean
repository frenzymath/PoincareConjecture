import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineFrameNormalization
import Mathlib.Analysis.Complex.Tietze

/-!
# Ambient extension of normalized operator fields

Finite-dimensional Tietze extension followed by affine frame
normalization extends continuous field data from a closed subset,
retaining their exact values and fixed frame. See Cairns 1940,
Section 8, p. 804, and M76 derivation 46.
-/

set_option autoImplicit false

open Set ContinuousLinearMap

namespace ContinuousMap

variable {X E F : Type*} [TopologicalSpace X] [NormalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Extend a continuous normalized field from any closed set
to the entire ambient source, with exact restriction and frame
normalization. See Cairns p. 804 and M76 derivation 46. -/
theorem exists_frame_extension {s : Set X} (hs : IsClosed s)
    (f : C(s, E →L[ℝ] F)) (J : F →L[ℝ] E) (Q0 : E →L[ℝ] F)
    (h0 : Function.RightInverse J Q0) (hf : ∀ x, Function.RightInverse J (f x)) :
    ∃ g : C(X, E →L[ℝ] F), (∀ x, Function.RightInverse J (g x)) ∧
      ∀ x : s, g x = f x := by
  obtain ⟨g, hg⟩ := f.exists_restrict_eq hs
  refine ⟨⟨fun x => frameNormalize J Q0 (g x),
    (contDiff_frameNormalize J Q0 0).continuous.comp g.continuous⟩,
    fun x => rightInverse_frameNormalize J Q0 h0 (g x), ?_⟩
  intro x
  have hx : g x = f x := congrArg (fun k : C(s, E →L[ℝ] F) => k x) hg
  change frameNormalize J Q0 (g x) = f x
  rw [hx, frameNormalize_eq_self J Q0 (f x) (hf x)]

end ContinuousMap
