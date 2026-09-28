import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalDiskAttachmentComplement
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition









set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_original_annulus_realization
    {E X α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {R D S : Set X}
    (F : X → E) (hFi : InjOn F R)
    (K : SimplicialComplex ℝ E) (hKs : K.space = F '' R)
    (H : R ≃ₜ K.space) (hH : ∀ x : R, (H x : E) = F x)
    (g : E → R) (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space)
    (hfrontR : frontier D ⊆ R) (hfrontD : frontier D ⊆ D) (hSR : S ⊆ R)
    {J B : Set E} (hJ : J = F '' (D ∩ frontier R))
    (ann : Ann ≃ₜ (F '' frontier D \ (J \ B) : Set E)) (hann : ann.IsFinitePL)
    (hannboundary : ∀ z : Ann, (ann z : E) ∈ J ↔
      depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1)
    {C : Set P2} (hC : C ⊆ Ann)
    (hphysical : Subtype.val '' (ann '' (Subtype.val ⁻¹' C : Set Ann)) = F '' S) :
    ∃ p : P2 → X, PolyhedralPLInCharts e p Ann ∧ InjOn p Ann ∧
      p '' Ann ⊆ frontier D ∧
      p '' {z | -1 < depth 8 z ∧ depth 8 z < 1} ⊆ interior R ∧
      p '' C = S ∧ ∀ z : Ann, F (p z) = (ann z : E) := by
  classical
  obtain ⟨a,ha,haval⟩ := hann
  have haK : MapsTo a Ann K.space := by
    intro z hz
    rw [←haval ⟨z,hz⟩,hKs]
    exact image_mono hfrontR (ann ⟨z,hz⟩).property.1
  have hFg (z : E) (hz : z ∈ K.space) : F (g z) = z := by
    rw [hg ⟨z,hz⟩,←hH (H.symm ⟨z,hz⟩),H.apply_symm_apply]
  let p : P2 → X := fun z => g (a z)
  have hpF (z : Ann) : F (p z) = (ann z : E) :=
    (hFg (a z) (haK z.property)).trans (haval z).symm
  have hpR (z : P2) : p z ∈ R := (g (a z)).property
  have hpPL : PolyhedralPLInCharts e p Ann := by
    obtain ⟨T,hT,hTs,hAffine⟩ := ha
    rw [←hTs]
    exact hgPL.comp_finitePiecewiseAffineOn T hT ⟨T,hT,rfl,hAffine⟩
      (fun z hz => haK (hTs.subset hz))
  have hpi : InjOn p Ann := by
    intro x hx y hy hxy
    have heq : ann ⟨x,hx⟩ = ann ⟨y,hy⟩ :=
      Subtype.ext ((hpF ⟨x,hx⟩).symm.trans ((congrArg F hxy).trans (hpF ⟨y,hy⟩)))
    exact congrArg Subtype.val (ann.injective heq)
  have hpfront (z : P2) (hz : z ∈ Ann) : p z ∈ frontier D := by
    have hFfront : F (p z) ∈ F '' frontier D := by
      rw [hpF ⟨z,hz⟩]
      exact (ann ⟨z,hz⟩).property.1
    obtain ⟨x,hx,hxeq⟩ := hFfront
    exact hFi (hfrontR hx) (hpR z) hxeq ▸ hx
  have hpint (z : P2) (hz : -1 < depth 8 z ∧ depth 8 z < 1) : p z ∈ interior R := by
    have hzAnn : z ∈ Ann := mem_squareAnnulus_iff_depth.mpr ⟨hz.1.le,hz.2.le⟩
    rw [←self_sdiff_frontier]
    refine ⟨hpR z,?_⟩
    intro hn
    have hzJ : (ann ⟨z,hzAnn⟩ : E) ∈ J := by
      rw [←hpF ⟨z,hzAnn⟩,hJ]
      exact ⟨p z,⟨hfrontD (hpfront z hzAnn),hn⟩,rfl⟩
    rcases (hannboundary ⟨z,hzAnn⟩).mp hzJ with hh | hh <;> linarith
  have himage : p '' C = S := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      have hi : (ann ⟨z,hC hz⟩ : E) ∈ F '' S :=
        hphysical.subset ⟨ann ⟨z,hC hz⟩,⟨⟨z,hC hz⟩,hz,rfl⟩,rfl⟩
      obtain ⟨x,hx,hxeq⟩ := hi
      have hxp := hFi (hSR hx) (hpR z) (hxeq.trans (hpF ⟨z,hC hz⟩).symm)
      exact hxp ▸ hx
    · intro x hx
      obtain ⟨_,⟨z,hz,rfl⟩,hzeq⟩ := hphysical.symm.subset (mem_image_of_mem F hx)
      exact ⟨z,hz,hFi (hpR z) (hSR hx) ((hpF z).trans hzeq)⟩
  refine ⟨p,hpPL,hpi,?_,?_,himage,hpF⟩
  · rintro _ ⟨z,hz,rfl⟩
    exact hpfront z hz
  · rintro _ ⟨z,hz,rfl⟩
    exact hpint z hz

end PoincareConjecture.M76

