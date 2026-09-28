import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Charts.RetainedBoundaryCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.PLAtlasTransport
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLDomainMaps
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalDomainCharts
import PoincareConjecture.Proofs.M76.Mathlib.AffineHalfspaceSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineProd










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem retained_pullback_chart_transition
    {X E ι κ : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {W : Set E} (G : X ≃ₜ W)
    (e : ι → OpenPartialHomeomorph X V3)
    (atlas : κ → OpenPartialHomeomorph W V3)
    (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hrep : ∀ j, ∃ (A : Set E) (f : E → V3), FinitePiecewiseAffineOn f A ∧
      ∀ x ∈ (atlas j).source, (x : E) ∈ A ∧ atlas j x = f x)
    {U : Set X} (hU : IsOpen U) (hG : ∀ x ∈ U, (G x : E) = F x) :
    ∀ i j, ((e i).restrOpen U hU).symm.trans
      (G.transOpenPartialHomeomorph (atlas j)) ∈ piecewiseAffineGroupoid V3 := by
  intro i j
  let Q := (e i).restrOpen U hU
  let q := G.symm.transOpenPartialHomeomorph Q
  have hq : LocallyPiecewiseAffineOn (fun z => (q.symm z : E)) q.target := by
    apply ((hF i).mono q.open_target (fun z hz => hz.1)).congr
    intro z hz
    exact (hG ((e i).symm z) hz.2).symm
  obtain ⟨A,f,hf,hval⟩ := hrep j
  have ht := q.mem_piecewiseAffineGroupoid_transition_of_locallyPL_inverse (atlas j) hq hf
    (fun x hx => (hval x hx).1) (fun x hx => (hval x hx).2)
  have hpull := homeomorph_pullback_chart_transition G q (atlas j)
  have hcancel : G.transOpenPartialHomeomorph q = Q :=
    homeomorph_pullback_chart_cancel G.symm Q
  rw [hcancel] at hpull
  exact hpull.symm ▸ ht

theorem chartwisePLOn_identity_of_restricted_transitions
    {X ι κ : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (d : κ → OpenPartialHomeomorph X V3)
    (he : PLDomain e Set.univ) (hd : PLDomain d Set.univ)
    {U : Set X} (hU : IsOpen U)
    (htrans : ∀ i j, ((e i).restrOpen U hU).symm.trans (d j) ∈
      piecewiseAffineGroupoid V3) :
    ChartwisePLOn e d (ContinuousMap.id (Set.univ : Set X))
      ((Subtype.val : ↥(Set.univ : Set X) → X) ⁻¹' U) := by
  refine ⟨he,hd,hU.preimage continuous_subtype_val,?_⟩
  intro x hx
  obtain ⟨i,hxi⟩ := he.cover x
  obtain ⟨j,hxj⟩ := hd.cover x
  let H := ((e i).restrOpen U hU).symm.trans (d j)
  have hxH : e i x ∈ H.source := by
    refine ⟨⟨(e i).map_source hxi,?_⟩,?_⟩
    · change (e i).symm (e i x) ∈ U
      rwa [(e i).left_inv hxi]
    · change (e i).symm (e i x) ∈ (d j).source
      rwa [(e i).left_inv hxi]
  obtain ⟨K,hK,hxK,hKH,hPL⟩ := (htrans i j).1 (e i x) hxH
  let V : Set (Set.univ : Set X) := (Subtype.val : ↥(Set.univ : Set X) → X) ⁻¹'
    ((e i).source ∩ (e i) ⁻¹' interior K.space)
  have hV : IsOpen V :=
    ((e i).isOpen_inter_preimage isOpen_interior).preimage continuous_subtype_val
  have hVU : V ⊆ (Subtype.val : ↥(Set.univ : Set X) → X) ⁻¹' U := by
    intro y hy
    have hu := (hKH (interior_subset hy.2)).1.2
    change (e i).symm (e i y) ∈ U at hu
    rwa [(e i).left_inv hy.1] at hu
  refine ⟨i,j,K,V,H,hK,hV,⟨hxi,hxK⟩,hVU,fun y hy => hy.1,?_,
    fun z hz => (hKH hz).1.1,?_,hPL.finitePiecewiseAffineOn hK,?_⟩
  · rintro z ⟨y,hy,rfl⟩
    exact interior_subset hy.2
  · intro z hz
    exact ⟨⟨(e i).symm z,mem_univ _⟩,(hKH hz).1.2,rfl⟩
  · intro y hy hyK
    have ht := (hKH hyK).2
    change (e i).symm (e i y) ∈ (d j).source at ht
    refine ⟨?_,?_⟩
    · simpa only [ContinuousMap.id_apply,(e i).left_inv hy] using ht
    · change d j ((e i).symm (e i y)) = d j y
      rw [(e i).left_inv hy]

theorem restricted_transition_reverse
    {X ι κ : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (d : κ → OpenPartialHomeomorph X V3)
    {U : Set X} (hU : IsOpen U)
    (htrans : ∀ i j, ((e i).restrOpen U hU).symm.trans (d j) ∈
      piecewiseAffineGroupoid V3) :
    ∀ j i, ((d j).restrOpen U hU).symm.trans (e i) ∈ piecewiseAffineGroupoid V3 := by
  intro j i
  have hrev := (piecewiseAffineGroupoid V3).symm (htrans i j)
  have heq : (((e i).restrOpen U hU).symm.trans (d j)).symm =
      ((d j).restrOpen U hU).symm.trans (e i) := by
    apply OpenPartialHomeomorph.ext
    · intro z
      rfl
    · intro z
      rfl
    · ext z
      change (z ∈ (d j).target ∧ (d j).symm z ∈ (e i).source ∩ U) ↔
        ((z ∈ (d j).target ∧ (d j).symm z ∈ U) ∧ (d j).symm z ∈ (e i).source)
      simp only [mem_inter_iff]
      tauto
  exact heq ▸ hrev

theorem chartwisePLOn_identity_domain_of_restricted_transitions
    {X ι κ : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (d : κ → OpenPartialHomeomorph X V3) {R : Set X}
    (he : PLDomain e R) (hd : PLDomain d R)
    {U : Set X} (hU : IsOpen U)
    (htrans : ∀ i j, ((e i).restrOpen U hU).symm.trans (d j) ∈
      piecewiseAffineGroupoid V3) :
    ChartwisePLOn e d (ContinuousMap.id R) ((Subtype.val : R → X) ⁻¹' U) := by
  classical
  refine ⟨he,hd,hU.preimage continuous_subtype_val,?_⟩
  intro x hx
  obtain ⟨i,hxi⟩ := he.cover x
  obtain ⟨j,hxj⟩ := hd.cover x
  obtain ⟨B,hxB,hB,hkind⟩ := he.exists_local_region_chart x
  let Q := (e i).restrOpen U hU
  let T := B.symm.trans Q
  let H := Q.symm.trans (d j)
  let D := T.trans H
  have hBi : B.symm.trans (e i) ∈ piecewiseAffineGroupoid V3 := by
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm] using (piecewiseAffineGroupoid V3).symm (hB i)
  have hT : T ∈ piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward T).mpr
    exact hBi.1.mono T.open_source (fun _ hz => ⟨hz.1,hz.2.1⟩)
  have hD : D ∈ piecewiseAffineGroupoid V3 :=
    (piecewiseAffineGroupoid V3).trans hT (htrans i j)
  have hxT : B x ∈ T.source := by
    refine ⟨B.map_source hxB,?_⟩
    change B.symm (B x) ∈ (e i).source ∩ U
    rw [B.left_inv hxB]
    exact ⟨hxi,hx⟩
  have hxD : B x ∈ D.source := by
    refine ⟨hxT,?_⟩
    have hxv : T (B x) = e i x := by change e i (B.symm (B x)) = _; rw [B.left_inv hxB]
    change T (B x) ∈ H.source
    rw [hxv]
    refine ⟨⟨(e i).map_source hxi,?_⟩,?_⟩
    · change (e i).symm (e i x) ∈ U
      rwa [(e i).left_inv hxi]
    · change (e i).symm (e i x) ∈ (d j).source
      rwa [(e i).left_inv hxi]
  have hF := hT.1.mono D.open_source (fun _ hz => hz.1)
  obtain ⟨J,hJ,hxJ,hJD,hfaces⟩ := (hF.prod_mk hD.1) (B x) hxD
  have hJtarget : J.space ⊆ B.target := fun z hz => (hJD hz).1.1
  have hclip : ∃ P : SimplicialComplex ℝ V3, P.faces.Finite ∧
      P.space ⊆ J.space ∧ ∀ z ∈ J.space, z ∈ P.space ↔ B.symm z ∈ R := by
    rcases hkind with hinside | ⟨ell,v,hv,hzero,hhalf⟩
    · refine ⟨J,hJ,subset_rfl,?_⟩
      intro z hz
      exact iff_of_true hz (hinside (B.map_target (hJtarget hz)))
    · obtain ⟨P,hP,hPs⟩ := J.exists_finite_triangulation_inter_halfspaces hJ {-ell.toAffineMap}
      refine ⟨P,hP,hPs.subset.trans inter_subset_left,?_⟩
      intro z hz
      rw [hPs]
      simp only [mem_inter_iff,hz,true_and,mem_ofPred_eq,Finset.mem_singleton,forall_eq]
      rw [hhalf (B.symm z) (B.map_target (hJtarget hz)),B.right_inv (hJtarget hz)]
      change -ell z ≤ 0 ↔ 0 ≤ ell z
      exact neg_nonpos
  obtain ⟨P,hP,hPJ,hPR⟩ := hclip
  have hPR' (z : V3) (hz : z ∈ P.space) : B.symm z ∈ R := (hPR z (hPJ hz)).mp hz
  have hPT (z : V3) (hz : z ∈ P.space) : z ∈ T.source := (hJD (hPJ hz)).1
  have hTD (z : V3) (hz : z ∈ P.space) : D z = d j (B.symm z) := by
    change d j (Q.symm (Q (B.symm z))) = _
    have hzQ : B.symm z ∈ Q.source := (hPT z hz).2
    rw [Q.left_inv hzQ]
  have hTP : FinitePiecewiseAffineOn T P.space :=
    ((hfaces.postcomp (ContinuousLinearMap.fst ℝ V3 V3).toContinuousAffineMap).finitePiecewiseAffineOn
      hJ).restrict P hP hPJ
  have hDP : FinitePiecewiseAffineOn D P.space :=
    ((hfaces.postcomp (ContinuousLinearMap.snd ℝ V3 V3).toContinuousAffineMap).finitePiecewiseAffineOn
      hJ).restrict P hP hPJ
  have hinv := hTP.inverse (g := T.symm) (fun z hz => T.left_inv (hPT z hz))
  obtain ⟨K,hK,hKs,hKinv⟩ := hinv
  have hKP (z : V3) (hz : z ∈ K.space) : T.symm z ∈ P.space := by
    obtain ⟨w,hw,rfl⟩ := hKs.subset hz
    rwa [T.left_inv (hPT w hw)]
  have hformula : FinitePiecewiseAffineOn (D ∘ T.symm) K.space :=
    hDP.comp (hKinv.finitePiecewiseAffineOn hK) (fun z hz => hKP z hz)
  let V : Set R := (Subtype.val : R → X) ⁻¹'
    (B.source ∩ B ⁻¹' interior J.space)
  have hV : IsOpen V :=
    (B.isOpen_inter_preimage isOpen_interior).preimage continuous_subtype_val
  have hVP (y : R) (hy : y ∈ V) : B y ∈ P.space :=
    (hPR (B y) (interior_subset hy.2)).mpr (by rw [B.left_inv hy.1]; exact y.property)
  have hVT (y : R) (hy : y ∈ V) : T (B y) = e i y := by
    change e i (B.symm (B y)) = _
    rw [B.left_inv hy.1]
  have hVU : V ⊆ (Subtype.val : R → X) ⁻¹' U := by
    intro y hy
    have h := (hPT (B y) (hVP y hy)).2.2
    change B.symm (B y) ∈ U at h
    rwa [B.left_inv hy.1] at h
  refine ⟨i,j,K,V,D ∘ T.symm,hK,hV,⟨hxB,hxJ⟩,hVU,?_,?_,?_,?_,hformula,?_⟩
  · intro y hy
    have h := (hPT (B y) (hVP y hy)).2.1
    change B.symm (B y) ∈ (e i).source at h
    rwa [B.left_inv hy.1] at h
  · rintro z ⟨y,hy,rfl⟩
    exact hKs.symm.subset ⟨B y,hVP y hy,hVT y hy⟩
  · intro z hz
    obtain ⟨w,hw,rfl⟩ := hKs.subset hz
    exact (T.map_source (hPT w hw)).1.1
  · intro z hz
    obtain ⟨w,hw,rfl⟩ := hKs.subset hz
    refine ⟨⟨B.symm w,hPR' w hw⟩,(hPT w hw).2.2,?_⟩
    exact ((e i).left_inv (hPT w hw).2.1).symm
  · intro y hy hyK
    obtain ⟨w,hw,heq⟩ := hKs.subset hyK
    have hwv : B.symm w = (y : X) := (e i).injOn (hPT w hw).2.1 hy heq
    have hsource := (hJD (hPJ hw)).2.2
    change Q.symm (Q (B.symm w)) ∈ (d j).source at hsource
    have hwQ : B.symm w ∈ Q.source := (hPT w hw).2
    rw [Q.left_inv hwQ,hwv] at hsource
    refine ⟨hsource,?_⟩
    change D (T.symm (e i y)) = d j y
    rw [← heq,T.left_inv (hPT w hw),hTD w hw,hwv]

theorem chartwisePLOn_identity_domain_both_of_restricted_transitions
    {X ι κ : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (d : κ → OpenPartialHomeomorph X V3) {R : Set X}
    (he : PLDomain e R) (hd : PLDomain d R)
    {U : Set X} (hU : IsOpen U)
    (htrans : ∀ i j, ((e i).restrOpen U hU).symm.trans (d j) ∈
      piecewiseAffineGroupoid V3) :
    ChartwisePLOn e d (ContinuousMap.id R) ((Subtype.val : R → X) ⁻¹' U) ∧
    ChartwisePLOn d e (ContinuousMap.id R) ((Subtype.val : R → X) ⁻¹' U) :=
  ⟨chartwisePLOn_identity_domain_of_restricted_transitions e d he hd hU htrans,
    chartwisePLOn_identity_domain_of_restricted_transitions d e hd he hU
      (restricted_transition_reverse e d hU htrans)⟩

theorem retained_pullback_identity_certificates
    {X E ι κ : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {W : Set E} (G : X ≃ₜ W)
    (e : ι → OpenPartialHomeomorph X V3)
    (atlas : κ → OpenPartialHomeomorph W V3)
    (he : PLDomain e Set.univ) (hatlas : PLDomain atlas Set.univ)
    (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hrep : ∀ j, ∃ (A : Set E) (f : E → V3), FinitePiecewiseAffineOn f A ∧
      ∀ x ∈ (atlas j).source, (x : E) ∈ A ∧ atlas j x = f x)
    {U : Set X} (hU : IsOpen U) (hG : ∀ x ∈ U, (G x : E) = F x) :
    let d := fun j => G.transOpenPartialHomeomorph (atlas j)
    ChartwisePLOn e d (ContinuousMap.id (Set.univ : Set X))
      ((Subtype.val : ↥(Set.univ : Set X) → X) ⁻¹' U) ∧
    ChartwisePLOn d e (ContinuousMap.id (Set.univ : Set X))
      ((Subtype.val : ↥(Set.univ : Set X) → X) ⁻¹' U) := by
  let d := fun j => G.transOpenPartialHomeomorph (atlas j)
  have hd : PLDomain d Set.univ := by
    simpa only [preimage_univ] using hatlas.preimage_homeomorph G
  have ht := retained_pullback_chart_transition G e atlas F hF hrep hU hG
  exact ⟨chartwisePLOn_identity_of_restricted_transitions e d he hd hU ht,
    chartwisePLOn_identity_of_restricted_transitions d e hd he hU
      (restricted_transition_reverse e d hU ht)⟩

end PoincareConjecture.M76
