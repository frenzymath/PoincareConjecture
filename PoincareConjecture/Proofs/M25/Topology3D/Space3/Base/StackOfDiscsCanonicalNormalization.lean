import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsScaleEvolution
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCanonicalEvolution











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D


noncomputable def stackCapCanonicalEndpoint
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (C : SurgeryCapTag psi u)
    (rFlat rOne v0 v1 lambda : ℝ) (q : UnitTwoSphere) : E3 :=
  let a := stackCanonicalHorizontal v0 v1
  let b := stackCanonicalVertical rFlat rOne
  let M := stackCapProfilePath a a b b 0
  C.tube ((M (heightCoordinates (q : E3))).1,
    C.cutHeight + C.sign *
      (C.removal + lambda * (M (heightCoordinates (q : E3))).2))


theorem exists_stackCapCanonicalNormalization
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (C : SurgeryCapTag psi u) (hpsi : IsCollarEmbedding psi)
    (K L : Set E3) (hK : IsCompact K) (hL : IsCompact L)
    (gap : ℝ) (hgap : 0 < gap)
    (hcover : range (fun q => psi (q, 0)) = K ∪ C.cap ∪ L)
    (hseam : C.seam ⊆ K)
    (hKside : ∀ y ∈ K, 0 ≤ C.sign * (inner ℝ (u : E3) y -
      (C.cutHeight + C.sign * C.removal)))
    (hLside : ∀ y ∈ L, gap ≤ C.sign * (inner ℝ (u : E3) y -
      (C.cutHeight + C.sign * C.removal)))
    (rFlat rOne v0 v1 : ℝ)
    (hrFlat : 0 < rFlat) (hradii : rFlat < rOne) (hrOne : rOne < 1)
    (hv0 : 0 < v0) (hv01 : v0 < v1) (hv1 : v1 < 1)
    (hprofileGap : v1 ^ 2 + rOne ^ 2 < 1)
    (gammaMatch gammaGraph : ℝ)
    (hgammaMatch : 0 < gammaMatch) (hgammaGraph : 0 < gammaGraph) :
    let a := stackCanonicalHorizontal v0 v1
    let b := stackCanonicalVertical rFlat rOne
    let seamHeight := C.cutHeight + C.sign * C.removal
    let chi := fun y : E3 => C.sign * (inner ℝ (u : E3) y - seamHeight)
    let eta := min gammaMatch (min gammaGraph (C.removal / 2)) / 2
    let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    ∃ B lambda : ℝ,
      1 ≤ B ∧ 0 < lambda ∧ lambda < C.scale ∧ lambda * B < eta ∧
      (∀ t : ℝ, ∀ q : UnitTwoSphere,
        |(stackCapProfilePath C.profile.horizontal a C.profile.vertical b t
          (heightCoordinates (q : E3))).2| ≤ B) ∧
      ∃ FA FB : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      ∃ SA NB KB : Set E3,
        let F := FA.trans FB
        let S := SA ∪ KB
        let Nopp := Sᶜ
        let endpoint := stackCapCanonicalEndpoint C rFlat rOne v0 v1 lambda
        IsCompact SA ∧ IsCompact KB ∧ IsOpen NB ∧
        C.seam ⊆ NB ∧ NB ⊆ C.tube.target ∧
        SA ⊆ C.tube.target ∩ {y | chi y < gap / 2} ∧
        KB ⊆ ((C.tube.target ∩
          {y | |inner ℝ (u : E3) y - seamHeight| < eta}) ∩
          {y | chi y < 0}) \ NB ∧
        tsupport (fun y => FA y - y) ⊆ SA ∧
        tsupport (fun y => FA.symm y - y) ⊆ SA ∧
        tsupport (fun y => FB y - y) ⊆ KB ∧
        tsupport (fun y => FB.symm y - y) ⊆ KB ∧
        (∀ y, y ∉ SA → FA y = y ∧ FA.symm y = y) ∧
        (∀ y, y ∉ KB → FB y = y ∧ FB.symm y = y) ∧
        (∀ y ∈ NB, FB y = y ∧ FB.symm y = y) ∧
        (∀ y, 0 ≤ chi y → FB y = y ∧ FB.symm y = y) ∧
        FA '' K = K ∧ FA.symm '' K = K ∧
        (∀ q ∈ Qminus,
          FA (C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale q) =
            C.profile.capMap C.tube C.cutHeight C.sign C.removal lambda q) ∧
        (∀ q ∈ Qminus,
          FB (C.profile.capMap C.tube C.cutHeight C.sign C.removal lambda q) =
            endpoint q) ∧
        IsCollarEmbedding (fun p => F (psi p)) ∧
        IsCompact S ∧ IsOpen Nopp ∧ L ⊆ Nopp ∧ Disjoint S L ∧
        S ⊆ C.tube.target ∩ {y | chi y < gap / 2} ∧
        tsupport (fun y => F y - y) ⊆ S ∧
        tsupport (fun y => F.symm y - y) ⊆ S ∧
        (∀ y, y ∉ S → F y = y ∧ F.symm y = y) ∧
        (∀ y ∈ Nopp, F y = y ∧ F.symm y = y) ∧
        (∀ y, gap / 2 ≤ chi y → F y = y ∧ F.symm y = y) ∧
        F '' K = K ∧ F.symm '' K = K ∧
        (∀ y ∈ C.seam, F y = y ∧ F.symm y = y) ∧
        (∀ q ∈ Qminus,
          F (C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale q) =
            endpoint q) ∧
        F '' C.cap = endpoint '' Qminus ∧
        F.symm '' (endpoint '' Qminus) = C.cap ∧
        K ∩ (endpoint '' Qminus) = C.seam ∧
        Disjoint (endpoint '' Qminus) L ∧
        (∀ q : UnitTwoSphere, F (psi (q, 0)) ∈ K ↔ psi (q, 0) ∈ K) ∧
        range (fun q => F (psi (q, 0))) = K ∪ (endpoint '' Qminus) ∪ L ∧
        lambda < gammaMatch / 2 ∧ lambda < gammaGraph / 2 ∧
        lambda < C.removal / 4 ∧
        ∀ q ∈ Qminus, -lambda ≤ chi (endpoint q) ∧ chi (endpoint q) ≤ 0 ∧
          |inner ℝ (u : E3) (endpoint q) - seamHeight| < gammaMatch ∧
          |inner ℝ (u : E3) (endpoint q) - seamHeight| < gammaGraph := by
  classical
  dsimp only
  let a := stackCanonicalHorizontal v0 v1
  let b := stackCanonicalVertical rFlat rOne
  let seamHeight := C.cutHeight + C.sign * C.removal
  let chi := fun y : E3 => C.sign * (inner ℝ (u : E3) y - seamHeight)
  let eta := min gammaMatch (min gammaGraph (C.removal / 2)) / 2
  let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  obtain ⟨B, lambda, hB, hlambda, hsmall, hlambdaB, hbound,
      NB, PhiB, KB, hNB, hcircleNB, hNBtube, _, _, _, _, _, hBfinal,
      hBheight, hKBcompact, hKB, hBsupp, hBsuppi, hBfix, hBfixNB, hBfixSide⟩ :=
    exists_stackCanonicalProfileEvolution C rFlat rOne v0 v1
      hrFlat hradii hrOne hv0 hv01 hv1 hprofileGap
      gammaMatch gammaGraph hgammaMatch hgammaGraph
  obtain ⟨PhiA, SA, NA, d, o, w, _, _, _, hSAcompact, _, _, _, _, _, _, _, hSA,
      hAsupp, hAsuppi, hAfix, hAcore, hAseamL, ho, _, _, _, hAtrack, _, _⟩ :=
    exists_stackCapScaleEvolution C hpsi K L hK hL gap lambda hgap hlambda hsmall
      hcover hseam hKside hLside
  let FA := PhiA 1
  let FB := PhiB 1
  let F := FA.trans FB
  let S := SA ∪ KB
  let Nopp := Sᶜ
  let endpoint := stackCapCanonicalEndpoint C rFlat rOne v0 v1 lambda
  have htime : (1 : ℝ) ∈ Ioo (-1 : ℝ) 2 := by norm_num
  obtain ⟨_, _, _, _, _, hstart, hfinish, _, _, hnonpos, hzero, _⟩ :=
    stackCapScaleCap_spec C lambda hlambda hsmall
  have hAfinal (q : UnitTwoSphere) (hq : q ∈ Qminus) :
      FA (C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale q) =
        C.profile.capMap C.tube C.cutHeight C.sign C.removal lambda q :=
    (hAtrack 1 htime q (hq.trans_lt ho)).trans (hfinish q)
  have hBendpoint (q : UnitTwoSphere) (hq : q ∈ Qminus) :
      FB (C.profile.capMap C.tube C.cutHeight C.sign C.removal lambda q) =
        endpoint q := hBfinal q hq
  have hseamNB : C.seam ⊆ NB := by
    rw [C.seam_eq_image]
    rintro y ⟨q, hq, rfl⟩
    change (heightCoordinates (q : E3)).2 = 0 at hq
    have hmodel : C.profile.model q =
        ((circleDirection (heightCoordinates (q : E3)).1 : E2), 0) := by
      simpa only [SurgeryCapProfile.model, hq] using
        surgeryCapModel_cylinder C.profile.horizontal C.profile.vertical
          C.profile.horizontal_smooth C.profile.vertical_smooth
          (fun z => (C.profile.horizontal_pos z).ne')
          (fun x => (C.profile.vertical_pos x).ne')
          C.profile.horizontal_near C.profile.vertical_far q
          (by rw [hq]; norm_num)
    apply hcircleNB
    refine ⟨((circleDirection (heightCoordinates (q : E3)).1 : E2), seamHeight),
      ⟨(circleDirection (heightCoordinates (q : E3)).1).property, rfl⟩, ?_⟩
    change C.tube ((circleDirection (heightCoordinates (q : E3)).1 : E2), seamHeight) =
      C.tube ((C.profile.model q).1, C.cutHeight + C.sign *
        (C.removal + C.scale * (C.profile.model q).2))
    rw [hmodel]
    simp only [mul_zero, add_zero, seamHeight]
  have hSAbound : SA ⊆ C.tube.target ∩ {y | chi y < gap / 2} :=
    fun _ hy => (hSA hy).1
  have hKBbound : KB ⊆ C.tube.target ∩ {y | chi y < gap / 2} := by
    intro y hy
    exact ⟨(hKB hy).1.1.1, ((hKB hy).1.2).trans (half_pos hgap)⟩
  have hSbound : S ⊆ C.tube.target ∩ {y | chi y < gap / 2} :=
    union_subset hSAbound hKBbound
  have hSc : IsCompact S := hSAcompact.union hKBcompact
  have hNopp : IsOpen Nopp := hSc.isClosed.isOpen_compl
  have hfixS (y : E3) (hy : y ∉ S) : F y = y ∧ F.symm y = y := by
    have hyA : y ∉ SA := fun h => hy (Or.inl h)
    have hyB : y ∉ KB := fun h => hy (Or.inr h)
    constructor
    · change FB (FA y) = y
      rw [(hAfix 1 y hyA).1, (hBfix 1 y hyB).1]
    · change FA.symm (FB.symm y) = y
      rw [(hBfix 1 y hyB).2, (hAfix 1 y hyA).2]
  have hFsupp : tsupport (fun y => F y - y) ⊆ S := by
    apply closure_minimal ?_ hSc.isClosed
    intro y hy
    by_contra hn
    exact hy (sub_eq_zero.mpr (hfixS y hn).1)
  have hFsuppi : tsupport (fun y => F.symm y - y) ⊆ S := by
    apply closure_minimal ?_ hSc.isClosed
    intro y hy
    by_contra hn
    exact hy (sub_eq_zero.mpr (hfixS y hn).2)
  have hLopp : L ⊆ Nopp := by
    intro y hy hys
    have hs : chi y < gap / 2 := (hSbound hys).2
    have hl : gap ≤ chi y := hLside y hy
    linarith only [hs, hl, hgap]
  have hSL : Disjoint S L := disjoint_left.mpr (fun _ hys hyL => hLopp hyL hys)
  have hfixNopp : ∀ y ∈ Nopp, F y = y ∧ F.symm y = y :=
    fun y hy => hfixS y hy
  have hFhalf (y : E3) (hy : gap / 2 ≤ chi y) : F y = y ∧ F.symm y = y :=
    hfixS y (fun hys => not_lt_of_ge hy (hSbound hys).2)
  have hBcore : FB '' K = K := by
    apply Set.EqOn.image_eq_self
    intro y hy
    exact (hBfixSide 1 y (hKside y hy)).1
  have hBcorei : FB.symm '' K = K := by
    apply Set.EqOn.image_eq_self
    intro y hy
    exact (hBfixSide 1 y (hKside y hy)).2
  have hFcore : F '' K = K := by
    calc
      F '' K = FB '' (FA '' K) := (image_image FB FA K).symm
      _ = K := by rw [(hAcore 1).1, hBcore]
  have hFcorei : F.symm '' K = K := by
    calc
      F.symm '' K = FA.symm '' (FB.symm '' K) :=
        (image_image FA.symm FB.symm K).symm
      _ = K := by rw [hBcorei, (hAcore 1).2]
  have hFseam (y : E3) (hy : y ∈ C.seam) : F y = y ∧ F.symm y = y := by
    constructor
    · change FB (FA y) = y
      rw [(hAseamL 1 y (Or.inl hy)).1, (hBfixNB 1 y (hseamNB hy)).1]
    · change FA.symm (FB.symm y) = y
      rw [(hBfixNB 1 y (hseamNB hy)).2, (hAseamL 1 y (Or.inl hy)).2]
  have hFtrack (q : UnitTwoSphere) (hq : q ∈ Qminus) :
      F (C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale q) =
        endpoint q := by
    change FB (FA _) = endpoint q
    rw [hAfinal q hq, hBendpoint q hq]
  have hcollar : IsCollarEmbedding (fun p => F (psi p)) := by
    refine ⟨F.contMDiff.comp_contMDiffOn hpsi.1, ?_, ?_⟩
    · intro x hx y hy hxy
      exact hpsi.2.1 hx hy (F.injective hxy)
    · intro p hp
      have hdpsi := (hpsi.1.contMDiffAt
        ((isOpen_univ.prod isOpen_Ioo).mem_nhds hp)).mdifferentiableAt (by simp)
      have hdF := (F.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective
        (x := psi p) (mem_univ _)
      change Function.Injective
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ((F : E3 → E3) ∘ psi) p)
      rw [mfderiv_comp p (F.mdifferentiable (by simp) (psi p)) hdpsi]
      exact hdF.comp (hpsi.2.2 p hp)
  have hcapimage : F '' C.cap = endpoint '' Qminus := by
    rw [C.cap_eq_image, image_image]
    apply image_congr
    intro q hq
    exact hFtrack q hq
  have hcapimagei : F.symm '' (endpoint '' Qminus) = C.cap := by
    rw [← hcapimage, image_image]
    simp only [Diffeomorph.symm_apply_apply, image_id']
  have hseamcap : C.seam ⊆ C.cap := by
    rw [C.seam_eq_image, C.cap_eq_image]
    exact image_mono (fun q hq => hq.le)
  have hcapK : K ∩ C.cap = C.seam := by
    apply Subset.antisymm
    · rintro y ⟨hyK, hycap⟩
      rw [C.cap_eq_image] at hycap
      obtain ⟨q, hq, rfl⟩ := hycap
      have hn := hnonpos 0 q hq
      rw [hstart q] at hn
      have hz : C.sign * (inner ℝ (u : E3)
          (C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale q) -
          (C.cutHeight + C.sign * C.removal)) = 0 :=
        le_antisymm hn (hKside _ hyK)
      have hq0 := (hzero 0 q hq).mp (by simpa only [hstart q] using hz)
      rw [C.seam_eq_image]
      exact ⟨q, hq0, rfl⟩
    · exact fun _ hy => ⟨hseam hy, hseamcap hy⟩
  have hcapL : Disjoint C.cap L := by
    apply disjoint_left.mpr
    intro y hy hyL
    rw [C.cap_eq_image] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    have hn := hnonpos 0 q hq
    rw [hstart q] at hn
    exact (not_le_of_gt hgap) ((hLside _ hyL).trans hn)
  have hcoreiff (y : E3) : F y ∈ K ↔ y ∈ K := by
    constructor
    · intro hy
      have hi : F.symm (F y) ∈ F.symm '' K := ⟨F y, hy, rfl⟩
      rw [hFcorei] at hi
      simpa only [Diffeomorph.symm_apply_apply] using hi
    · intro hy
      rw [← hFcore]
      exact ⟨y, hy, rfl⟩
  have hnewinter : K ∩ (endpoint '' Qminus) = C.seam := by
    rw [← hcapimage]
    apply Subset.antisymm
    · rintro y ⟨hyK, x, hx, rfl⟩
      have hxS : x ∈ C.seam := hcapK ▸ ⟨(hcoreiff x).mp hyK, hx⟩
      simpa only [(hFseam x hxS).1] using hxS
    · intro y hy
      exact ⟨hseam hy, y, hseamcap hy, (hFseam y hy).1⟩
  have hFL (y : E3) (hy : y ∈ L) : F y = y := (hfixNopp y (hLopp hy)).1
  have hFimageL : F '' L = L := by
    apply Set.EqOn.image_eq_self
    exact hFL
  have hnewL : Disjoint (endpoint '' Qminus) L := by
    rw [← hcapimage]
    apply disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ hyL
    have hxy : x = F x := F.injective (hFL (F x) hyL).symm
    exact disjoint_left.mp hcapL hx (hxy.symm ▸ hyL)
  have hnewcover : range (fun q => F (psi (q, 0))) =
      K ∪ (endpoint '' Qminus) ∪ L := by
    calc
      range (fun q => F (psi (q, 0))) = F '' range (fun q => psi (q, 0)) :=
        range_comp' F (fun q => psi (q, 0))
      _ = K ∪ (endpoint '' Qminus) ∪ L := by
        rw [hcover, image_union, image_union, hFcore, hcapimage, hFimageL]
  have hlambda_le : lambda ≤ lambda * B := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hB hlambda.le
  have hlambda_eta : lambda < eta := hlambda_le.trans_lt hlambdaB
  have hetaMatch : eta ≤ gammaMatch / 2 :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hetaGraph : eta ≤ gammaGraph / 2 :=
    div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _))
      (by norm_num)
  have hetaRemoval : eta ≤ C.removal / 4 := by
    have hmin : min gammaMatch (min gammaGraph (C.removal / 2)) ≤ C.removal / 2 :=
      (min_le_right _ _).trans (min_le_right _ _)
    dsimp only [eta]
    linarith only [hmin]
  have hlambdaMatch : lambda < gammaMatch / 2 := hlambda_eta.trans_le hetaMatch
  have hlambdaGraph : lambda < gammaGraph / 2 := hlambda_eta.trans_le hetaGraph
  have hlambdaRemoval : lambda < C.removal / 4 := hlambda_eta.trans_le hetaRemoval
  have hMone (p : E2 × ℝ) :
      stackCapProfilePath C.profile.horizontal a C.profile.vertical b 1 p =
        stackCapProfilePath a a b b 0 p := by
    simp only [stackCapProfilePath,
      stackProfileBlend_of_one_le C.profile.horizontal a 1 le_rfl,
      stackProfileBlend_of_one_le C.profile.vertical b 1 le_rfl,
      stackProfileBlend_of_nonpos a a 0 le_rfl,
      stackProfileBlend_of_nonpos b b 0 le_rfl]
  have hcapone (q : UnitTwoSphere) :
      stackPlacedProfileCap C.profile.horizontal a C.profile.vertical b
        C.tube C.cutHeight C.sign C.removal lambda 1 q = endpoint q := by
    change C.tube _ = C.tube _
    simp only [hMone, a, b]
  have hfinalheight (q : UnitTwoSphere) (hq : q ∈ Qminus) :
      -lambda ≤ chi (endpoint q) ∧ chi (endpoint q) ≤ 0 ∧
      |inner ℝ (u : E3) (endpoint q) - seamHeight| < gammaMatch ∧
      |inner ℝ (u : E3) (endpoint q) - seamHeight| < gammaGraph := by
    have hh := hBheight q hq
    rw [hcapone q] at hh
    have habschi : |chi (endpoint q)| ≤ lambda := by
      rw [abs_of_nonpos hh.2]
      linarith only [hh.1]
    have habseq : |chi (endpoint q)| =
        |inner ℝ (u : E3) (endpoint q) - seamHeight| := by
      dsimp only [chi]
      rw [abs_mul, C.sign_abs, one_mul]
    rw [habseq] at habschi
    refine ⟨hh.1, hh.2, habschi.trans_lt ?_, habschi.trans_lt ?_⟩
    · linarith only [hlambdaMatch, hgammaMatch]
    · linarith only [hlambdaGraph, hgammaGraph]
  exact ⟨B, lambda, hB, hlambda, hsmall, hlambdaB, hbound,
    FA, FB, SA, NB, KB, hSAcompact, hKBcompact, hNB, hseamNB, hNBtube,
    hSAbound, hKB, hAsupp 1, hAsuppi 1, hBsupp 1, hBsuppi 1,
    hAfix 1, hBfix 1, hBfixNB 1, hBfixSide 1,
    (hAcore 1).1, (hAcore 1).2, hAfinal, hBendpoint,
    hcollar, hSc, hNopp, hLopp, hSL, hSbound, hFsupp, hFsuppi,
    hfixS, hfixNopp, hFhalf, hFcore, hFcorei, hFseam, hFtrack,
    hcapimage, hcapimagei, hnewinter, hnewL,
    (fun q => hcoreiff (psi (q, 0))), hnewcover,
    hlambdaMatch, hlambdaGraph, hlambdaRemoval, hfinalheight⟩

end PoincareConjecture.M25.Topology3D
