import PoincareConjecture.Proofs.M76.Mathlib.CollarLevelCapIncidence
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLLevelReplacement
import PoincareConjecture.Proofs.M76.Mathlib.OriginalCollarLevelCharts
import PoincareConjecture.Proofs.M76.Mathlib.PointedCollarSourcePartition
import PoincareConjecture.Proofs.M76.Mathlib.PointedRimArcPartition

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

theorem bijOn_ambient_representative {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {s : Set X} {t : Set Y}
    (e : s ≃ₜ t) {f : X → Y} (hf : ∀ x : s, (e x : Y) = f x) : BijOn f s t := by
  refine ⟨fun x hx => ?_, ?_, ?_⟩
  · rw [← hf ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).property
  · intro x hx y hy hxy
    have heq : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa only [hf] using hxy
    exact congrArg Subtype.val (e.injective heq)
  · intro y hy
    refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, ?_⟩
    rw [← hf, e.apply_symm_apply]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePL.exists_pointed_whole_level_comparison_with_selected
    {B T d b k R : Set E} {upper g r : E → ℝ} {q : E}
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    (hdplane : d ⊆ {x | A x = 0}) (hcap : d ∩ T = b)
    (hresidual : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (C p : E) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    (H : E ≃ₜ E) (hfix : ∀ x ∈ R, H x = x)
    (hB : B = b ∪ k) (htouch : b ∩ k ⊆ {q}) (hqzero : upper q = 0)
    (hgr : EqOn g r b) (hgk : ∀ x ∈ k, g x = 0)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKk : K.space = k)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJR : J.space = R)
    {t a : ℝ} (ht : 0 < t) (hc : 0 < t * a)
    (hhigh : ∀ x ∈ b, a ≤ r x → t * a < upper x)
    (hwidth : IsFinitePLBallPair ℝ (b ∩ {x | t * a ≤ upper x})
      (b ∩ {x | upper x = t * a}))
    {L : {x : E | x ∈ B ∧ t * a ∈ Icc (t * g x) (upper x)} ≃ₜ
      ((H '' T) ∩ {x | A x = t * a} : Set E)} (hL : L.IsFinitePL)
    (hLres : ∀ x : {x : E | x ∈ B ∧ t * a ∈ Icc (t * g x) (upper x)},
      (L x : E) ∈ R ↔ upper x = t * a)
    (hLp : ∀ x : {x : E | x ∈ B ∧ t * a ∈ Icc (t * g x) (upper x)},
      ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
        (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H (C p) ∧
        (t * g x = t * a ↔ (p : E × ℝ).2 = 0) ∧
        (upper x = t * a ↔ (p : E × ℝ).2 = upper x))
    {f : E → E} (hfval : ∀ x, (L x : E) = f x)
    (hball : IsFinitePLBallPair ℝ
      (((H '' d) ∩ {x | A x = t * a}) ∪
        f '' ((b ∩ {x | r x ≤ a}) ∩ {x | t * a ≤ upper x}))
      (f '' (b ∩ {x | upper x = t * a})))
    (harcR : (((H '' d) ∩ {x | A x = t * a}) ∪
        f '' ((b ∩ {x | r x ≤ a}) ∩ {x | t * a ≤ upper x})) ∩ R =
      f '' (b ∩ {x | upper x = t * a})) :
    ∃ F : ((T ∪ R) ∩ {x | A x = t * a} : Set E) ≃ₜ
        (((H '' (d ∪ T)) ∪ R) ∩ {x | A x = t * a} : Set E),
      F.IsFinitePL ∧
      (∀ x : (R ∩ {x | A x = t * a} : Set E),
        (F ⟨x, ⟨Or.inr x.property.1, x.property.2⟩⟩ : E) = x) ∧
      (∀ (p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)})
          (_hb : (p : E × ℝ).1 ∈ b) (hz : (p : E × ℝ).2 = t * a),
        (F ⟨C p, ⟨Or.inl (C p).property, (hheight p).trans hz⟩⟩ : E) ∈
          ((H '' d) ∩ {x | A x = t * a}) ∪
            f '' ((b ∩ {x | r x ≤ a}) ∩ {x | t * a ≤ upper x})) ∧
      ∀ (x : E) (hxk : x ∈ k) (hxu : t * a ≤ upper x),
        ∃ z : ((T ∪ R) ∩ {x | A x = t * a} : Set E),
          (z : E) = C ⟨(x, t * a), hB.symm.subset (Or.inr hxk), hc.le, hxu⟩ ∧
          (F z : E) = f x := by
  let S₀ : Set E := {x | x ∈ B ∧ t * a ≤ upper x}
  let S₁ : Set E := {x | x ∈ B ∧ t * a ∈ Icc (t * g x) (upper x)}
  let u : Set E := b ∩ {x | t * a ≤ upper x}
  let j : Set E := (b ∩ {x | r x ≤ a}) ∩ {x | t * a ≤ upper x}
  let w : Set E := k ∩ {x | t * a ≤ upper x}
  let e : Set E := b ∩ {x | upper x = t * a}
  let Rc : Set E := R ∩ {x | A x = t * a}
  let cap : Set E := (H '' d) ∩ {x | A x = t * a}
  obtain ⟨hS₀, hS₁, huw, hjw⟩ :=
    pointed_collar_level_source_partition hB htouch hqzero hgr hgk ht hc
  have hw₀ : w ⊆ S₀ := subset_union_right.trans hS₀.symm.subset
  have hw₁ : w ⊆ S₁ := subset_union_right.trans hS₁.symm.subset
  have hu₀ : u ⊆ S₀ := subset_union_left.trans hS₀.symm.subset
  have hj₁ : j ⊆ S₁ := subset_union_left.trans hS₁.symm.subset
  have he₀ : e ⊆ S₀ := hwidth.1.trans hu₀
  obtain ⟨_, _, heJ⟩ := rim_superlevel_truncated_sublevel_partition hhigh
  have he₁ : e ⊆ S₁ := heJ.trans hj₁
  obtain ⟨L₀, hL₀, hL₀val⟩ := hC.exists_original_collar_level_chart A hheight hc.le
  obtain ⟨f₀, hf₀, hf₀val⟩ := hL₀
  have hbij₀ := L₀.bijOn_ambient_representative hf₀val
  have hbij₁ := L.bijOn_ambient_representative hfval
  obtain ⟨f', hf', hf'val⟩ := hL
  have hf : FinitePiecewiseAffineOn f S₁ :=
    hf'.congr (fun x hx => (hf'val ⟨x, hx⟩).symm.trans (hfval ⟨x, hx⟩))
  have hcopy := hf₀
  obtain ⟨N, hN, hNS, _⟩ := hcopy
  obtain ⟨W, hW, hWs⟩ := N.exists_finite_triangulation_inter K hN hK
  have hWw : W.space = w := by
    rw [hWs, hNS, hKk]
    ext x
    change ((x ∈ B ∧ t * a ≤ upper x) ∧ x ∈ k) ↔ x ∈ k ∧ t * a ≤ upper x
    exact ⟨fun hx => ⟨hx.2, hx.1.2⟩,
      fun hx => ⟨⟨hB.symm.subset (Or.inr hx.1), hx.2⟩, hx.1⟩⟩
  obtain ⟨Jc, hJc, hJcs⟩ := J.exists_finite_affineLevel_complex hJ A (t * a)
  have hJcR : Jc.space = Rc := by rw [hJcs, hJR]
  have hcontact₀ (x : S₀) : f₀ x ∈ Rc ↔ upper x = t * a := by
    have hlevel : A (f₀ x) = t * a := by
      rw [← hf₀val]
      exact (L₀ x).property.2
    have hmem : f₀ x ∈ R ↔ t * a = upper x := by
      rw [← hf₀val, hL₀val, hresidual]
    exact ⟨fun hx => (hmem.mp hx.1).symm,
      fun hx => ⟨hmem.mpr hx.symm, hlevel⟩⟩
  have hcontact₁ (x : S₁) : f x ∈ Rc ↔ upper x = t * a := by
    have hlevel : A (f x) = t * a := by rw [← hfval]; exact (L x).property.2
    have hmem : f x ∈ R ↔ upper x = t * a := by rw [← hfval]; exact hLres x
    exact ⟨fun hx => hmem.mp hx.1, fun hx => ⟨hmem.mpr hx, hlevel⟩⟩
  have hequal (x : E) (hx₀ : x ∈ S₀) (hx₁ : x ∈ S₁)
      (hxu : upper x = t * a) : f₀ x = f x := by
    obtain ⟨p, hpbase, hpval, _, hphi⟩ := hLp ⟨x, hx₁⟩
    have hptop := hphi.mp hxu
    have hpR : (C p : E) ∈ R :=
      (hresidual p).mpr (hptop.trans (congrArg upper hpbase).symm)
    have hCp : (C p : E) = f₀ x := by
      rw [← hf₀val ⟨x, hx₀⟩, hL₀val]
      exact congrArg (fun p => (C p : E))
        (Subtype.ext (Prod.ext hpbase (hptop.trans hxu)))
    exact hCp.symm.trans ((hfix _ hpR).symm.trans (hpval.symm.trans (hfval ⟨x, hx₁⟩)))
  have hcapw : Disjoint cap (f '' w) := by
    apply disjoint_left.mpr
    rintro y hy ⟨x, hx, rfl⟩
    have hmem : (L ⟨x, hw₁ hx⟩ : E) ∈ H '' d := by
      rw [hfval]
      exact hy.1
    have hinc := collar_level_mem_moved_cap_iff C hheight hbottom hdplane hcap H
      (fun x => (L x : E)) (fun x => by
        obtain ⟨p, hbase, hval, hlo, _⟩ := hLp x
        exact ⟨p, hbase, hval, hlo⟩) ⟨x, hw₁ hx⟩
    have hzero := (hinc.mp hmem).2
    rw [hgk x hx.1, mul_zero] at hzero
    exact hc.ne hzero
  have huR : (f₀ '' u) ∩ Rc = f₀ '' e := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hxR⟩
      exact ⟨x, ⟨hx.1, (hcontact₀ ⟨x, hu₀ hx⟩).mp hxR⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨mem_image_of_mem f₀ (hwidth.1 hx), (hcontact₀ ⟨x, he₀ hx⟩).mpr hx.2⟩
  have harcLevel : cap ∪ f '' j ⊆ {x | A x = t * a} := by
    rintro y (hy | ⟨x, hx, rfl⟩)
    · exact hy.2
    · rw [← hfval ⟨x, hj₁ hx⟩]
      exact (L ⟨x, hj₁ hx⟩).property.2
  have harcRc : (cap ∪ f '' j) ∩ Rc = f '' e := by
    change (cap ∪ f '' j) ∩ (R ∩ {x | A x = t * a}) = f '' e
    rw [← inter_assoc, inter_eq_left.mpr (inter_subset_left.trans harcLevel)]
    exact harcR
  obtain ⟨G, hG, hGR, hGw, hGu⟩ :=
    hf₀.exists_level_replacement_fixing_residual hf hbij₀.injOn hbij₁.injOn
      hS₀ hS₁ huw hjw hcapw hwidth hball huR harcRc
      (fun x hx => hequal x (he₀ hx) (he₁ hx) hx.2)
      (fun x hx => (hcontact₀ ⟨x, hw₀ hx⟩).trans (hcontact₁ ⟨x, hw₁ hx⟩).symm)
      (fun x hx hxR => hequal x (hw₀ hx) (hw₁ hx) ((hcontact₀ ⟨x, hw₀ hx⟩).mp hxR))
      W hW hWw Jc hJc hJcR
  have hsource : (f₀ '' S₀) ∪ Rc = (T ∪ R) ∩ {x | A x = t * a} := by
    rw [hbij₀.image_eq]
    exact (union_inter_distrib_right T R _).symm
  have htarget : (cap ∪ f '' S₁) ∪ Rc = ((H '' (d ∪ T)) ∪ R) ∩ {x | A x = t * a} := by
    rw [hbij₁.image_eq, image_union]
    simp only [cap, Rc, union_inter_distrib_right]
  let F := (Homeomorph.setCongr hsource.symm).trans
    (G.trans (Homeomorph.setCongr htarget))
  refine ⟨F, hG.setCongr hsource htarget, fun x => hGR x, ?_, ?_⟩
  · intro p hpb hpz
    have hpu : (p : E × ℝ).1 ∈ u := ⟨hpb, hpz ▸ p.property.2.2⟩
    have hCp : (C p : E) ∈ f₀ '' u := by
      refine ⟨(p : E × ℝ).1, hpu, ?_⟩
      rw [← hf₀val ⟨(p : E × ℝ).1, hu₀ hpu⟩, hL₀val]
      exact congrArg (fun p => (C p : E)) (Subtype.ext (Prod.ext rfl hpz.symm))
    exact (hGu ⟨C p, Or.inl (image_mono hu₀ hCp)⟩).mp hCp
  · intro x hxk hxu
    let z : ((T ∪ R) ∩ {x | A x = t * a} : Set E) :=
      ⟨f₀ x, hsource.subset (Or.inl ⟨x, hw₀ ⟨hxk, hxu⟩, rfl⟩)⟩
    refine ⟨z, ?_, hGw ⟨x, hxk, hxu⟩⟩
    exact (hf₀val ⟨x, hw₀ ⟨hxk, hxu⟩⟩).symm.trans (hL₀val _)

theorem IsFinitePL.exists_pointed_whole_level_comparison
    {B T d b k R : Set E} {upper g r : E → ℝ} {q : E}
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    (hdplane : d ⊆ {x | A x = 0}) (hcap : d ∩ T = b)
    (hresidual : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (C p : E) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    (H : E ≃ₜ E) (hfix : ∀ x ∈ R, H x = x)
    (hB : B = b ∪ k) (htouch : b ∩ k ⊆ {q}) (hqzero : upper q = 0)
    (hgr : EqOn g r b) (hgk : ∀ x ∈ k, g x = 0)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKk : K.space = k)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJR : J.space = R)
    {t a : ℝ} (ht : 0 < t) (hc : 0 < t * a)
    (hhigh : ∀ x ∈ b, a ≤ r x → t * a < upper x)
    (hwidth : IsFinitePLBallPair ℝ (b ∩ {x | t * a ≤ upper x})
      (b ∩ {x | upper x = t * a}))
    {L : {x : E | x ∈ B ∧ t * a ∈ Icc (t * g x) (upper x)} ≃ₜ
      ((H '' T) ∩ {x | A x = t * a} : Set E)} (hL : L.IsFinitePL)
    (hLres : ∀ x : {x : E | x ∈ B ∧ t * a ∈ Icc (t * g x) (upper x)},
      (L x : E) ∈ R ↔ upper x = t * a)
    (hLp : ∀ x : {x : E | x ∈ B ∧ t * a ∈ Icc (t * g x) (upper x)},
      ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
        (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H (C p) ∧
        (t * g x = t * a ↔ (p : E × ℝ).2 = 0) ∧
        (upper x = t * a ↔ (p : E × ℝ).2 = upper x))
    {f : E → E} (hfval : ∀ x, (L x : E) = f x)
    (hball : IsFinitePLBallPair ℝ
      (((H '' d) ∩ {x | A x = t * a}) ∪
        f '' ((b ∩ {x | r x ≤ a}) ∩ {x | t * a ≤ upper x}))
      (f '' (b ∩ {x | upper x = t * a})))
    (harcR : (((H '' d) ∩ {x | A x = t * a}) ∪
        f '' ((b ∩ {x | r x ≤ a}) ∩ {x | t * a ≤ upper x})) ∩ R =
      f '' (b ∩ {x | upper x = t * a})) :
    ∃ F : ((T ∪ R) ∩ {x | A x = t * a} : Set E) ≃ₜ
        (((H '' (d ∪ T)) ∪ R) ∩ {x | A x = t * a} : Set E),
      F.IsFinitePL ∧
      (∀ x : (R ∩ {x | A x = t * a} : Set E),
        (F ⟨x, ⟨Or.inr x.property.1, x.property.2⟩⟩ : E) = x) ∧
      ∀ (x : E) (hxk : x ∈ k) (hxu : t * a ≤ upper x),
        ∃ z : ((T ∪ R) ∩ {x | A x = t * a} : Set E),
          (z : E) = C ⟨(x, t * a), hB.symm.subset (Or.inr hxk), hc.le, hxu⟩ ∧
          (F z : E) = f x := by
  obtain ⟨F, hF, hFR, _, hother⟩ :=
    hC.exists_pointed_whole_level_comparison_with_selected A hheight hbottom hdplane hcap
      hresidual H hfix hB htouch hqzero hgr hgk K hK hKk J hJ hJR ht hc
      hhigh hwidth hL hLres hLp hfval hball harcR
  exact ⟨F, hF, hFR, hother⟩

end Homeomorph
