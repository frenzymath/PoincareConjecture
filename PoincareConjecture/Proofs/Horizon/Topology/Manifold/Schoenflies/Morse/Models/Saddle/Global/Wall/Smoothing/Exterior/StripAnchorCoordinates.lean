import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Pasting
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Differential

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "IR" => 𝓘(Real, Real)
local notation "IR2" => 𝓘(Real, Real × Real)

theorem anchorStripParameter_coordinates
    {height : S2 → Real} {c t₀ : Real}
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (hheight : ∀ z ∈ F.source, height (F z) = c + z.2)
    (R : Real → Real ≃ₘ[Real] Real) (α : S1 → S2)
    (hlevel : ∀ q, height (α q) = c + t₀)
    {q : S1} (hq : α q ∈ F.target) :
    (R t₀ (anchorStripParameter F R t₀ α q), t₀) = F.symm (α q) := by
  have hh := hheight (F.symm (α q)) (F.map_target hq)
  rw [F.right_inv hq, hlevel q] at hh
  apply Prod.ext
  · exact (R t₀).apply_symm_apply (F.symm (α q)).1
  · linarith

theorem anchorStripParameter_reconstructs
    {height : S2 → Real} {c t₀ : Real}
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (hheight : ∀ z ∈ F.source, height (F z) = c + z.2)
    (R : Real → Real ≃ₘ[Real] Real) (α : S1 → S2)
    (hlevel : ∀ q, height (α q) = c + t₀)
    {q : S1} (hq : α q ∈ F.target) :
    F (R t₀ (anchorStripParameter F R t₀ α q), t₀) = α q := by
  rw [anchorStripParameter_coordinates F hheight R α hlevel hq]
  exact F.right_inv hq

theorem strip_anchor_parameter_geometry
    {height : S2 → Real} {c t₀ : Real}
    (α : S1 → S2) (hα : ContMDiff (𝓡 1) (𝓡 2) ∞ α)
    (hαinj : Injective α)
    (hαder : ∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) α q))
    (hlevel : ∀ q, height (α q) = c + t₀)
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (hF : ContMDiffOn IR2 (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) IR2 ∞ F.symm F.target)
    (hheight : ∀ z ∈ F.source, height (F z) = c + z.2)
    (R : Real → Real ≃ₘ[Real] Real)
    {U : Set S2} (hU : IsOpen U) (hUtarget : U ⊆ F.target) :
    ContMDiffOn (𝓡 1) IR ∞ (anchorStripParameter F R t₀ α) (α ⁻¹' U) ∧
      InjOn (anchorStripParameter F R t₀ α) (α ⁻¹' U) ∧
      ∀ q ∈ α ⁻¹' U,
        Injective (mfderiv (𝓡 1) IR (anchorStripParameter F R t₀ α) q) := by
  let σ := anchorStripParameter F R t₀ α
  let line : Real → Real × Real := fun s => (R t₀ s, t₀)
  have hV : IsOpen (α ⁻¹' U) := hU.preimage hα.continuous
  have hcoords : ContMDiffOn (𝓡 1) IR2 ∞ (fun q => F.symm (α q)) (α ⁻¹' U) :=
    hFi.comp hα.contMDiffOn (fun q hq => hUtarget hq)
  have hσ : ContMDiffOn (𝓡 1) IR ∞ σ (α ⁻¹' U) := by
    apply (R t₀).symm.contMDiff.comp_contMDiffOn
    exact (contDiff_fst : ContDiff Real ∞ (Prod.fst : Real × Real → Real)).contMDiff
      |>.comp_contMDiffOn hcoords
  have hfactor (q : S1) (hq : q ∈ α ⁻¹' U) : F (line (σ q)) = α q :=
    anchorStripParameter_reconstructs F hheight R α hlevel (hUtarget hq)
  refine ⟨hσ, ?_, ?_⟩
  · intro q hq z hz hqz
    apply hαinj
    calc
      α q = F (line (σ q)) := (hfactor q hq).symm
      _ = F (line (σ z)) := congrArg (fun s => F (line s)) hqz
      _ = α z := hfactor z hz
  · intro q hq
    have hσq := hσ.contMDiffAt (hV.mem_nhds hq)
    have hline : ContMDiff IR IR2 ∞ line :=
      ((R t₀).contDiff.prodMk contDiff_const).contMDiff
    have hsource : line (σ q) ∈ F.source := by
      change (R t₀ (anchorStripParameter F R t₀ α q), t₀) ∈ F.source
      rw [anchorStripParameter_coordinates F hheight R α hlevel (hUtarget hq)]
      exact F.map_target (hUtarget hq)
    have houter : ContMDiffAt IR (𝓡 2) ∞ (F ∘ line) (σ q) :=
      (hF.contMDiffAt (F.open_source.mem_nhds hsource)).comp (σ q) (hline (σ q))
    have heq : α =ᶠ[𝓝 q] (F ∘ line) ∘ σ := by
      filter_upwards [hV.mem_nhds hq] with z hz
      exact (hfactor z hz).symm
    have hd := hαder q
    rw [heq.mfderiv_eq (I := 𝓡 1) (I' := 𝓡 2),
      mfderiv_comp q (houter.mdifferentiableAt (by simp))
        (hσq.mdifferentiableAt (by simp))] at hd
    intro u v huv
    apply hd
    exact congrArg (mfderiv IR (𝓡 2) (F ∘ line) (σ q)) huv

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior
