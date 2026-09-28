import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalDiskAttachmentComplement
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalBoundaryMarks
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.RimCircleCoordinates

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_original_annular_disk_realization
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
    {C d rim : Set P2}
    (hphysical : Subtype.val '' (ann '' (Subtype.val ⁻¹' C : Set Ann)) = F '' S)
    (hd : IsFinitePLBallPair P2 d rim)
    (hdinside : d ⊆ {z | -1 < depth 8 z ∧ depth 8 z < 1})
    (hcontacts : d ∩ C = rim) :
    ∃ p : P2 → X, PolyhedralPLInCharts e p d ∧ InjOn p d ∧
      p '' d ⊆ frontier D ∩ interior R ∧ p '' d ∩ S = p '' rim ∧
      ∀ z ∈ d, ∃ z' : Ann, (z' : P2) = z ∧ F (p z) = (ann z' : E) := by
  classical
  have hdAnn : d ⊆ Ann := fun z hz => mem_squareAnnulus_iff_depth.mpr
    ⟨(hdinside hz).1.le,(hdinside hz).2.le⟩
  obtain ⟨a,ha,haval⟩ := hann
  have haK : MapsTo a d K.space := by
    intro z hz
    rw [←haval ⟨z,hdAnn hz⟩,hKs]
    exact (image_mono hfrontR) (ann ⟨z,hdAnn hz⟩).property.1
  have hFg (z : E) (hz : z ∈ K.space) : F (g z) = z := by
    rw [hg ⟨z,hz⟩,←hH (H.symm ⟨z,hz⟩),H.apply_symm_apply]
  let p : P2 → X := fun z => g (a z)
  have hpF (z : P2) (hz : z ∈ d) : F (p z) = (ann ⟨z,hdAnn hz⟩ : E) :=
    (hFg (a z) (haK hz)).trans (haval ⟨z,hdAnn hz⟩).symm
  have hpR (z : P2) : p z ∈ R := (g (a z)).property
  have hpPL : PolyhedralPLInCharts e p d := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨T,hT,hTd,_⟩,_⟩,_⟩ := hd
    rw [←hTd]
    exact hgPL.comp_finitePiecewiseAffineOn T hT
      (ha.restrict T hT (hTd.subset.trans hdAnn)) (fun z hz => haK (hTd.subset hz))
  have hpi : InjOn p d := by
    intro x hx y hy hxy
    have heq : ann ⟨x,hdAnn hx⟩ = ann ⟨y,hdAnn hy⟩ :=
      Subtype.ext ((hpF x hx).symm.trans ((congrArg F hxy).trans (hpF y hy)))
    exact congrArg Subtype.val (ann.injective heq)
  have hpfront (z : P2) (hz : z ∈ d) : p z ∈ frontier D := by
    have hFfront : F (p z) ∈ F '' frontier D := by
      rw [hpF z hz]
      exact (ann ⟨z,hdAnn hz⟩).property.1
    obtain ⟨x,hx,hxeq⟩ := hFfront
    exact hFi (hfrontR hx) (hpR z) hxeq ▸ hx
  have hpint (z : P2) (hz : z ∈ d) : p z ∈ interior R := by
    rw [←self_sdiff_frontier]
    refine ⟨hpR z,?_⟩
    intro hn
    have hzJ : (ann ⟨z,hdAnn hz⟩ : E) ∈ J := by
      rw [←hpF z hz,hJ]
      exact ⟨p z,⟨hfrontD (hpfront z hz),hn⟩,rfl⟩
    have hh := (hannboundary ⟨z,hdAnn hz⟩).mp hzJ
    rcases hh with hh | hh <;> linarith [(hdinside hz).1,(hdinside hz).2]
  have hmem (z : P2) (hz : z ∈ d) : p z ∈ S ↔ z ∈ C := by
    constructor
    · intro hzS
      have hi := hphysical.symm.subset (mem_image_of_mem F hzS)
      obtain ⟨_,⟨w,hw,rfl⟩,hweq⟩ := hi
      have hwz := ann.injective (Subtype.ext (hweq.trans (hpF z hz)))
      change (w : P2) ∈ C at hw
      have hwz' : (w : P2) = z := congrArg Subtype.val hwz
      rwa [hwz'] at hw
    · intro hzC
      have hi : (ann ⟨z,hdAnn hz⟩ : E) ∈ F '' S :=
        hphysical.subset ⟨ann ⟨z,hdAnn hz⟩,⟨⟨z,hdAnn hz⟩,hzC,rfl⟩,rfl⟩
      obtain ⟨x,hx,hxeq⟩ := hi
      have hxp := hFi (hSR hx) (hpR z) (hxeq.trans (hpF z hz).symm)
      exact hxp ▸ hx
  refine ⟨p,hpPL,hpi,?_,?_,?_⟩
  · rintro _ ⟨z,hz,rfl⟩
    exact ⟨hpfront z hz,hpint z hz⟩
  · apply Subset.antisymm
    · rintro _ ⟨⟨z,hz,rfl⟩,hzS⟩
      exact ⟨z,hcontacts.subset ⟨hz,(hmem z hz).mp hzS⟩,rfl⟩
    · rintro _ ⟨z,hz,rfl⟩
      have hh := hcontacts.symm.subset hz
      exact ⟨⟨z,hh.1,rfl⟩,(hmem z hh.1).mpr hh.2⟩
  · intro z hz
    exact ⟨⟨z,hdAnn hz⟩,rfl,hpF z hz⟩

theorem exists_original_annular_frontier_pole
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X]
    {R D U : Set X} (F : X → E) (hFi : InjOn F R)
    (hfrontR : frontier D ⊆ R) (hDR : D ⊆ R) (hU : U ⊆ interior R)
    {J B : Set E} (hJ : J = F '' (D ∩ frontier R))
    (ann : Ann ≃ₜ (F '' frontier D \ (J \ B) : Set E))
    (hannboundary : ∀ z : Ann, (ann z : E) ∈ J ↔
      depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1) :
    ∃ p : X, p ∈ frontier D ∩ frontier R ∧ p ∉ U := by
  let z := Dehn.annulusRimPoint false 0
  have hzdepth : depth 8 (z : P2) = -1 := by
    simpa only [Bool.false_eq_true,if_false] using Dehn.depth_annulusRimPoint false 0
  have hzJ : (ann z : E) ∈ F '' (D ∩ frontier R) :=
    hJ.subset ((hannboundary z).mpr (Or.inl hzdepth))
  obtain ⟨x,hx,hxeq⟩ := hzJ
  obtain ⟨y,hy,hyeq⟩ := (ann z).property.1
  have hxy := hFi (hDR hx.1) (hfrontR hy) (hxeq.trans hyeq.symm)
  refine ⟨x,⟨hxy.symm ▸ hy,hx.2⟩,?_⟩
  exact fun hu => hx.2.2 (hU hu)

end PoincareConjecture.M76
