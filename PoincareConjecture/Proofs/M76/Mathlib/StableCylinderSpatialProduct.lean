import PoincareConjecture.Proofs.M76.Mathlib.StableCylinderConjugation
import PoincareConjecture.Proofs.M76.Mathlib.AddCircleShortArcCharts
import Mathlib.Topology.Covering.AddCircle

set_option autoImplicit false

open Set

namespace StableCylinder

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem isLocalHomeomorphOn_shortArc_spatial
    (p : ℝ) [Fact (0 < p)] {delta : ℝ} (hd1 : delta ≤ 1) (hdp : delta < p / 2)
    (f : X × ℝ → Y × ℝ)
    (hf : IsLocalHomeomorphOn f (univ ×ˢ Ioo (-1) 1)) :
    let q := AddCircle.shortArcQuotient p delta
    IsLocalHomeomorphOn
      (fun z : X × AddCircle p =>
        ((f (z.1, q.symm z.2)).1, ((f (z.1, q.symm z.2)).2 : AddCircle p)))
      (univ ×ˢ q.target) := by
  let q := AddCircle.shortArcQuotient p delta
  let Q := (OpenPartialHomeomorph.refl X).prod q.symm
  have hQ : MapsTo Q Q.source (univ ×ˢ Ioo (-1) 1) := by
    intro z hz
    have hs : q.symm z.2 ∈ Ioo (-delta) delta := by
      rw [← AddCircle.shortArcQuotient_source p hdp]
      exact q.map_target hz.2
    refine ⟨mem_univ _, ?_⟩
    change q.symm z.2 ∈ Ioo (-1) 1
    constructor <;> linarith [hs.1, hs.2]
  have hi : IsLocalHomeomorphOn (id : Y → Y) univ :=
    (Homeomorph.refl Y).isLocalHomeomorph.isLocalHomeomorphOn
  have hc : IsLocalHomeomorphOn ((↑) : ℝ → AddCircle p) univ :=
    (AddCircle.isLocalHomeomorph_coe p).isLocalHomeomorphOn
  have hp : IsLocalHomeomorphOn
      (fun z : Y × ℝ => (z.1, (z.2 : AddCircle p))) univ :=
    (hi.prodMap hc).mono (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
  exact hp.comp (hf.comp (IsLocalHomeomorphOn.OpenPartialHomeomorph.isLocalHomeomorphOn Q)
    hQ) (fun _ _ => mem_univ _)

theorem exists_spatial_product
    (p : ℝ) [Fact (0 < p)] {delta a : ℝ}
    (_hd : 0 < delta) (hd1 : delta ≤ 1) (hdp : delta < p / 2) (hda : delta ≤ a)
    (L : (AddCircle p × ℝ) ≃ₜ (AddCircle p × ℝ))
    (hL : MapsTo L (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1))
    (hrot : ∀ s : ℝ, |s| ≤ a → ∀ t : ℝ, |t| ≤ a →
      L ((s : AddCircle p), t) = (((-t : ℝ) : AddCircle p), s))
    (hinv : ∀ s : ℝ, |s| ≤ a → ∀ t : ℝ, |t| ≤ a →
      L.symm ((s : AddCircle p), t) = ((t : AddCircle p), -s))
    (f : X × ℝ → Y × ℝ) (g : X → Y) (U : Set X) (hU : IsOpen U)
    (hf : IsLocalHomeomorphOn f (univ ×ˢ Ioo (-1) 1))
    (hg : IsLocalHomeomorphOn g U)
    (hprod : EqOn f (fun z => (g z.1, z.2)) (U ×ˢ Ioo (-1) 1))
    (hheight : ∀ x : X, ∀ s : ℝ, |s| ≤ delta → |(f (x, s)).2| ≤ a) :
    let A := ((↑) : ℝ → AddCircle p) '' Ioo (-delta) delta
    let W := (U ×ˢ univ) ∪ (univ ×ˢ A)
    ∃ G : X × AddCircle p → Y × AddCircle p,
      IsLocalHomeomorphOn G W ∧
      EqOn G (fun z => (g z.1, z.2)) (U ×ˢ univ) ∧
      (∀ x : X, ∀ s ∈ Ioo (-delta) delta,
        G (x, (s : AddCircle p)) = ((f (x, s)).1, ((f (x, s)).2 : AddCircle p))) ∧
      EqOn (conjugation L f) (fun z => (G z.1, z.2)) (W ×ˢ Ioo (-delta) delta) ∧
      ∀ z ∈ W, ∃ t ∈ Ioo (-1) 1, (G z).1 = (f (z.1, t)).1 := by
  let q := AddCircle.shortArcQuotient p delta
  let V := U ×ˢ (univ : Set (AddCircle p))
  let N := (univ : Set X) ×ˢ q.target
  let g0 : X × AddCircle p → Y × AddCircle p := fun z => (g z.1, z.2)
  let g1 : X × AddCircle p → Y × AddCircle p := fun z =>
    ((f (z.1, q.symm z.2)).1, ((f (z.1, q.symm z.2)).2 : AddCircle p))
  have hqT : q.target = ((↑) : ℝ → AddCircle p) '' Ioo (-delta) delta :=
    AddCircle.shortArcQuotient_target p hdp
  have hqS : q.source = Ioo (-delta) delta := AddCircle.shortArcQuotient_source p hdp
  have hthin {s : ℝ} (hs : s ∈ Ioo (-delta) delta) : s ∈ Ioo (-1) 1 := by
    constructor <;> linarith [hs.1, hs.2]
  have hagree : EqOn g0 g1 (V ∩ N) := by
    intro z hz
    have hs : q.symm z.2 ∈ Ioo (-delta) delta := hqS ▸ q.map_target hz.2.2
    have hfval : f (z.1, q.symm z.2) = (g z.1, q.symm z.2) :=
      hprod ⟨hz.1.1, hthin hs⟩
    change (g z.1, z.2) =
      ((f (z.1, q.symm z.2)).1, ((f (z.1, q.symm z.2)).2 : AddCircle p))
    rw [hfval]
    exact Prod.ext rfl (q.right_inv hz.2.2).symm
  obtain ⟨G, hG, hG0, hG1⟩ := hg.prod_id.exists_union
    (isLocalHomeomorphOn_shortArc_spatial p hd1 hdp f hf)
    (hU.prod isOpen_univ) (isOpen_univ.prod q.open_target) hagree
  have hGarc (x : X) (s : ℝ) (hs : s ∈ Ioo (-delta) delta) :
      G (x, (s : AddCircle p)) = ((f (x, s)).1, ((f (x, s)).2 : AddCircle p)) := by
    rw [hG1 ⟨mem_univ _, q.map_source (hqS.symm ▸ hs)⟩]
    change ((f (x, q.symm (s : AddCircle p))).1,
      ((f (x, q.symm (s : AddCircle p))).2 : AddCircle p)) = _
    rw [AddCircle.shortArcQuotient_symm_coe p hdp hs]
  change ∃ G : X × AddCircle p → Y × AddCircle p, _
  have hW : (U ×ˢ univ) ∪
      (univ ×ˢ (((↑) : ℝ → AddCircle p) '' Ioo (-delta) delta)) = V ∪ N := by
    rw [← hqT]
  rw [hW]
  refine ⟨G, hG, hG0, hGarc, ?_, ?_⟩
  · intro z hz
    change conjugation L f z = (G z.1, z.2)
    rcases hz.1 with hzo | hzn
    · rw [conjugation_old_product L hL f g U hprod hzo.1 z.1.2 (hthin hz.2), hG0 hzo]
    · obtain ⟨s, hs, he⟩ := hqT ▸ hzn.2
      have hzval : z = ((z.1.1, (s : AddCircle p)), z.2) :=
        Prod.ext (Prod.ext rfl he.symm) rfl
      rw [hzval, conjugation_new_product L ((↑) : ℝ → AddCircle p) f hda hrot hinv
        hheight z.1.1 (abs_lt.mpr hs).le (abs_lt.mpr hz.2).le, hGarc z.1.1 s hs]
  · intro z hz
    rcases hz with hzo | hzn
    · refine ⟨0, by norm_num, ?_⟩
      rw [hG0 hzo, hprod ⟨hzo.1, by norm_num⟩]
    · have hs : q.symm z.2 ∈ Ioo (-delta) delta := hqS ▸ q.map_target hzn.2
      exact ⟨q.symm z.2, hthin hs, congrArg Prod.fst (hG1 hzn)⟩

end StableCylinder
