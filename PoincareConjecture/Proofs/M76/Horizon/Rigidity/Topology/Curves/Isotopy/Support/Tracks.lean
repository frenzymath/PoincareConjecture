import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Support.FiniteDimensionalSelection
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import Mathlib.Topology.UnitInterval

set_option autoImplicit false
open Set Geometry unitInterval

namespace PoincareConjecture.M76.CollarIsotopy

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

private theorem finitePL_interval_identity :
    FinitePiecewiseAffineOn (id : ℝ → ℝ) (Icc (0 : ℝ) 1) := by
  classical
  let A : Finset (ℝ →ᵃ[ℝ] ℝ) :=
    {-AffineMap.id ℝ ℝ, AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ 1}
  have hA : Icc (0 : ℝ) 1 = {x | ∀ a ∈ A, a x ≤ 0} := by
    ext x
    simp [A]
  obtain ⟨K, hK, hKs⟩ := isCompact_Icc.exists_finite_triangulation_of_halfspaces A hA
  exact ⟨K, hK, hKs, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩

theorem exists_conjugate_joint_finitePL {A : Set E} {C : Set F}
    (q : A ≃ₜ C) (hq : q.IsFinitePL) (H : I → A ≃ₜ A)
    (track : (ℝ × E) → E)
    (htrack : FinitePiecewiseAffineOn track (Icc (0 : ℝ) 1 ×ˢ A))
    (hvalue : ∀ t : I, ∀ x : A, track ((t : ℝ), x) = (H t x : E)) :
    ∃ g : (ℝ × F) → F,
      FinitePiecewiseAffineOn g (Icc (0 : ℝ) 1 ×ˢ C) ∧
      ∀ t : I, ∀ x : C, g ((t : ℝ), x) = (q (H t (q.symm x)) : F) := by
  obtain ⟨i, hi, hiv⟩ := hq.symm
  obtain ⟨f, hf, hfv⟩ := hq
  have him : MapsTo (Prod.map (id : ℝ → ℝ) i)
      (Icc (0 : ℝ) 1 ×ˢ C) (Icc (0 : ℝ) 1 ×ˢ A) := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    change i z.2 ∈ A
    rw [← hiv ⟨z.2, hz.2⟩]
    exact (q.symm ⟨z.2, hz.2⟩).property
  have htm : MapsTo track (Icc (0 : ℝ) 1 ×ˢ A) A := by
    intro z hz
    rw [hvalue ⟨z.1, hz.1⟩ ⟨z.2, hz.2⟩]
    exact (H ⟨z.1, hz.1⟩ ⟨z.2, hz.2⟩).property
  refine ⟨f ∘ track ∘ Prod.map id i,
    hf.comp (htrack.comp (finitePL_interval_identity.prodMap hi) him)
      (htm.comp him), ?_⟩
  intro t x
  change f (track ((t : ℝ), i x)) = _
  rw [← hiv x, hvalue, ← hfv]

theorem finitePiecewiseAffineOn_supported_track
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {C : Set E} (hC : IsClosed C) {track g : (ℝ × E) → E}
    (htrack : FinitePiecewiseAffineOn track (Icc (0 : ℝ) 1 ×ˢ C))
    (hg : ContinuousOn g (Icc (0 : ℝ) 1 ×ˢ K.space))
    (hgin : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K.space ∩ C,
      g (t, x) = track (t, x))
    (hgout : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K.space \ C, g (t, x) = x) :
    FinitePiecewiseAffineOn g (Icc (0 : ℝ) 1 ×ˢ K.space) := by
  have hkid : FinitePiecewiseAffineOn (id : E → E) K.space :=
    (K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)).finitePiecewiseAffineOn hK
  obtain ⟨J, hJ, hJs, _⟩ := finitePL_interval_identity.prodMap hkid
  have hsnd : FinitePiecewiseAffineOn (Prod.snd : ℝ × E → E) J.space :=
    (J.affineOnFaces_affine
      (ContinuousLinearMap.snd ℝ ℝ E).toContinuousAffineMap).finitePiecewiseAffineOn hJ
  rw [← hJs]
  apply hsnd.closed_paste_on_carrier_finiteDimensional J hJ (isClosed_Icc.prod hC)
    htrack (hJs.symm ▸ hg)
  · intro z hz
    exact hgin z.1 (hJs ▸ hz.1).1 z.2 ⟨(hJs ▸ hz.1).2, hz.2.2⟩
  · intro z hz
    exact hgout z.1 (hJs ▸ hz.1).1 z.2
      ⟨(hJs ▸ hz.1).2, fun hx => hz.2 ⟨(hJs ▸ hz.1).1, hx⟩⟩

end PoincareConjecture.M76.CollarIsotopy
