import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCommonBuffers
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsFullCapAlignment











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D




theorem exists_stackNonnestedLowerCapAlignment
    (P : SurgeryCapProfile) (U V : Fin 2 → OpenPartialHomeomorph (E2 × ℝ) E3)
    (hU : ∀ i, ContDiffOn ℝ ∞ (U i) (U i).source)
    (hUi : ∀ i, ContDiffOn ℝ ∞ (U i).symm (U i).target)
    (hV : ∀ i, ContDiffOn ℝ ∞ (V i) (V i).source)
    (hVi : ∀ i, ContDiffOn ℝ ∞ (V i).symm (V i).target)
    (u : UnitTwoSphere)
    (hUh : ∀ i p, p ∈ (U i).source → inner ℝ (u : E3) (U i p) = p.2)
    (hVh : ∀ i p, p ∈ (V i).source → inner ℝ (u : E3) (V i p) = p.2)
    (hUs : ∀ i, closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (U i).source)
    (hVs : ∀ i, closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (V i).source)
    (s tau : ℝ) (htau : 0 < tau)
    (hboundary : ∀ i z, z ∈ Icc (s - tau) (s + tau) →
      (fun x : E2 => U i (x, z)) '' sphere (0 : E2) 1 =
        (fun x : E2 => V i (x, z)) '' sphere (0 : E2) 1)
    (hsame : ∀ i,
      U i '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)) =
        V i '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)))
    (hdis : Disjoint
      (U 0 '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)))
      (U 1 '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ))))
    (R : Set E3) (hRheight : ∀ y ∈ R, s ≤ inner ℝ (u : E3) y)
    (hRband : ∀ y ∈ R, inner ℝ (u : E3) y ∈ Icc (s - tau) (s + tau) →
      ∃ i : Fin 2, y ∈ V i '' (sphere (0 : E2) 1 ×ˢ
        ({inner ℝ (u : E3) y} : Set ℝ)))
    (W : Fin 2 → Set E3) (hW : ∀ i, IsOpen (W i))
    (hUW : ∀ i, U i '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ⊆ W i) :
    ∃ eta bound : ℝ, 0 < eta ∧ eta < tau ∧ 1 ≤ bound ∧ P.heightBound ≤ bound ∧
      ∀ lambda : Fin 2 → ℝ, (∀ i, 0 < lambda i) → (∀ i, lambda i * bound < eta) →
        let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
        let CU := fun i => P.capMap (U i) s 1 0 (lambda i) '' Qminus
        let CV := fun i => P.capMap (V i) s 1 0 (lambda i) '' Qminus
        ∃ F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
          ∃ K : Set E3,
            (∀ i, F '' CU i = CV i ∧ F.symm '' CV i = CU i) ∧
            F '' (R ∪ CU 0 ∪ CU 1) = R ∪ CV 0 ∪ CV 1 ∧
            F.symm '' (R ∪ CV 0 ∪ CV 1) = R ∪ CU 0 ∪ CU 1 ∧
            (∀ y ∈ R, F y = y ∧ F.symm y = y) ∧
            IsCompact K ∧ K ⊆ W 0 ∪ W 1 ∧
            tsupport (fun y => F y - y) ⊆ K ∧
            tsupport (fun y => F.symm y - y) ⊆ K ∧
            ∀ y, y ∉ K → F y = y ∧ F.symm y = y := by
  classical
  obtain ⟨r, d, O, hr, hd, hdtau, hO, hOdis, hbuffer⟩ :=
    exists_stackCommonDiscBuffers U V s tau htau
      (fun i _ hp => hUs i ⟨hp.1, mem_univ _⟩)
      (fun i _ hp => hVs i ⟨hp.1, mem_univ _⟩) hsame hdis W hW hUW
  have hdisjoint (i j : Fin 2) (hij : i ≠ j) : Disjoint (O i) (O j) := by
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact hOdis
    · exact hOdis.symm
    · exact False.elim (hij rfl)
  obtain ⟨k, hk, hkrange, hkfix⟩ := exists_saddle_end_height_clamp
    (s - 3 * d / 4) (s + 3 * d / 4) (d / 4) (by linarith) (by positivity)
  have hkI (z : ℝ) : k z ∈ Icc (s - d) (s + d) := by
    have hz := hkrange z
    constructor <;> linarith [hz.1, hz.2]
  have hcircleO (i : Fin 2) :
      V i '' (sphere (0 : E2) 1 ×ˢ Icc (s - 3 * d / 4) (s + 3 * d / 4)) ⊆ O i := by
    rintro _ ⟨p, hp, rfl⟩
    apply (hbuffer i).2.2.2
    refine ⟨p, ⟨closedBall_subset_closedBall hr.le (sphere_subset_closedBall hp.1), ?_⟩, rfl⟩
    constructor <;> linarith [hp.2.1, hp.2.2]
  choose bounds hBounds hPBounds halign using fun i : Fin 2 =>
    exists_stackOriginalCapAlignment_in_height_band P (U i) (V i)
      (hU i) (hUi i) (hV i) (hVi i) u (hUh i) (hVh i) (hUs i) (hVs i)
      (Icc (s - d) (s + d)) isCompact_Icc
      (fun z hz => hboundary i z ⟨by linarith [hz.1], by linarith [hz.2]⟩)
      k hk hkI (s - d) (s - 3 * d / 4) (s - d / 2)
      (s + d / 2) (s + 3 * d / 4) (s + d)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      hkfix (O i) (hO i).1 (hcircleO i)
  let eta := d / 4
  let bound := max (bounds 0) (bounds 1)
  have hbi (i : Fin 2) : bounds i ≤ bound := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hbound : 1 ≤ bound := (hBounds 0).trans (hbi 0)
  have hPbound : P.heightBound ≤ bound := (hPBounds 0).trans (hbi 0)
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hetaD : eta < d := by dsimp only [eta]; linarith
  have hUstack (i : Fin 2) :
      U i '' (closedBall (0 : E2) 1 ×ˢ Icc (s - eta) (s + eta)) ⊆ O i := by
    apply Subset.trans ?_ (hbuffer i).2.2.1
    apply image_mono
    apply prod_mono (closedBall_subset_closedBall hr.le)
    exact Icc_subset_Icc (by linarith) (by linarith)
  have hVstack (i : Fin 2) :
      V i '' (closedBall (0 : E2) 1 ×ˢ Icc (s - eta) (s + eta)) ⊆ O i := by
    apply Subset.trans ?_ (hbuffer i).2.2.2
    apply image_mono
    apply prod_mono (closedBall_subset_closedBall hr.le)
    exact Icc_subset_Icc (by linarith) (by linarith)
  refine ⟨eta, bound, heta, hetaD.trans hdtau, hbound, hPbound, ?_⟩
  intro lambda hlambda hsmall
  dsimp only
  let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let CU := fun i => P.capMap (U i) s 1 0 (lambda i) '' Qminus
  let CV := fun i => P.capMap (V i) s 1 0 (lambda i) '' Qminus
  choose G K hGcap _hGcapInv hK hKO _hGs _hGsi hGfix hGprotected using fun i : Fin 2 =>
    halign i s 1 (lambda i) eta (by norm_num) (hlambda i)
      ((mul_le_mul_of_nonneg_left (hbi i) (hlambda i).le).trans_lt (hsmall i))
      (by dsimp only [eta]; linarith) (by dsimp only [eta]; linarith)
      (O i) (O i) (hO i).1 (hO i).1 (hUstack i) (hVstack i)
  have hKO' (i : Fin 2) : K i ⊆ O i := by
    intro y hy
    rcases hKO i hy with h | h
    · rcases h with h | h
      · exact h
      · exact h.1
    · exact h
  have hGR (i : Fin 2) (y : E3) (hy : y ∈ R) :
      G i y = y ∧ (G i).symm y = y := by
    apply hGprotected i y ?_ (Or.inl ?_)
    · by_cases hyO : y ∈ O i
      · by_cases hyH : inner ℝ (u : E3) y ∈ Ioo (s - 3 * d / 4) (s + 3 * d / 4)
        · obtain ⟨j, p, hp, hpy⟩ := hRband y hy
            ⟨by linarith [hyH.1], by linarith [hyH.2]⟩
          have hpz : p.2 = inner ℝ (u : E3) y := mem_singleton_iff.mp hp.2
          have hyOj : y ∈ O j := by
            apply (hbuffer j).2.2.2
            refine ⟨p, ⟨closedBall_subset_closedBall hr.le (sphere_subset_closedBall hp.1),
              ?_⟩, hpy⟩
            rw [hpz]
            constructor <;> linarith [hyH.1, hyH.2]
          have hji : j = i := by
            by_contra hji
            exact disjoint_left.mp (hdisjoint j i hji) hyOj hyO
          rw [hji] at hpy
          refine Or.inr (Or.inr ⟨p, ⟨hp.1, ?_⟩, hpy⟩)
          rw [hpz]
          exact ⟨hyH.1.le, hyH.2.le⟩
        · exact Or.inr (Or.inl hyH)
      · exact Or.inl hyO
    · simpa only [one_mul] using sub_nonneg.mpr (hRheight y hy)
  have hcapband (i : Fin 2) (q : UnitTwoSphere) :
      ((P.model q).1, s + lambda i * (P.model q).2) ∈
        closedBall (0 : E2) 1 ×ˢ Icc (s - eta) (s + eta) := by
    have hheight : |(P.model q).2| ≤ P.heightBound := P.height_bound q
    have hsmallP : lambda i * P.heightBound < eta :=
      (mul_le_mul_of_nonneg_left hPbound (hlambda i).le).trans_lt (hsmall i)
    have habs : |lambda i * (P.model q).2| < eta := by
      rw [abs_mul, abs_of_pos (hlambda i)]
      exact (mul_le_mul_of_nonneg_left hheight (hlambda i).le).trans_lt hsmallP
    refine ⟨mem_closedBall_zero_iff.mpr (P.model_fst_norm_le q), ?_⟩
    constructor <;> linarith [(abs_lt.mp habs).1, (abs_lt.mp habs).2]
  have hCUO (i : Fin 2) : CU i ⊆ O i := by
    rintro _ ⟨q, _hq, rfl⟩
    simp only [SurgeryCapProfile.capMap_apply, one_mul, zero_add]
    exact hUstack i ⟨_, hcapband i q, rfl⟩
  have hCVO (i : Fin 2) : CV i ⊆ O i := by
    rintro _ ⟨q, _hq, rfl⟩
    simp only [SurgeryCapProfile.capMap_apply, one_mul, zero_add]
    exact hVstack i ⟨_, hcapband i q, rfl⟩
  have hcross (i j : Fin 2) (hij : i ≠ j) (y : E3) (hy : y ∈ O j) :
      G i y = y ∧ (G i).symm y = y :=
    hGfix i y (fun hk => disjoint_left.mp (hdisjoint i j hij) (hKO' i hk) hy)
  let F := (G 0).trans (G 1)
  let Kall := K 0 ∪ K 1
  have hGcap' (i : Fin 2) : G i '' CU i = CV i := hGcap i
  have hFcap (i : Fin 2) : F '' CU i = CV i := by
    simp only [F, Diffeomorph.coe_trans, image_comp]
    fin_cases i
    · change G 1 '' (G 0 '' CU 0) = CV 0
      rw [hGcap' 0]
      exact EqOn.image_eq_self (fun y hy => (hcross 1 0 (by decide) y (hCVO 0 hy)).1)
    · change G 1 '' (G 0 '' CU 1) = CV 1
      have hfixed : G 0 '' CU 1 = CU 1 :=
        EqOn.image_eq_self (fun y hy => (hcross 0 1 (by decide) y (hCUO 1 hy)).1)
      rw [hfixed]
      exact hGcap 1
  have hFcapInv (i : Fin 2) : F.symm '' CV i = CU i := by
    rw [← hFcap i, image_image]
    simp only [F.symm_apply_apply, image_id']
  have hFR (y : E3) (hy : y ∈ R) : F y = y ∧ F.symm y = y := by
    have h0 := hGR 0 y hy
    have h1 := hGR 1 y hy
    change G 1 (G 0 y) = y ∧ (G 0).symm ((G 1).symm y) = y
    rw [h0.1, h1.1, h1.2, h0.2]
    exact ⟨rfl, rfl⟩
  have hKall : IsCompact Kall := (hK 0).union (hK 1)
  have hFfix (y : E3) (hy : y ∉ Kall) : F y = y ∧ F.symm y = y := by
    have h0 := hGfix 0 y (fun hk => hy (Or.inl hk))
    have h1 := hGfix 1 y (fun hk => hy (Or.inr hk))
    change G 1 (G 0 y) = y ∧ (G 0).symm ((G 1).symm y) = y
    rw [h0.1, h1.1, h1.2, h0.2]
    exact ⟨rfl, rfl⟩
  refine ⟨F, Kall, (fun i => ⟨hFcap i, hFcapInv i⟩), ?_, ?_, hFR, hKall,
    union_subset_union ((hKO' 0).trans (hO 0).2) ((hKO' 1).trans (hO 1).2), ?_, ?_, hFfix⟩
  · have hRimage : F '' R = R := EqOn.image_eq_self (fun y hy => (hFR y hy).1)
    rw [image_union, image_union, hRimage, hFcap 0, hFcap 1]
  · have hRimage : F.symm '' R = R := EqOn.image_eq_self (fun y hy => (hFR y hy).2)
    rw [image_union, image_union, hRimage, hFcapInv 0, hFcapInv 1]
  · apply closure_minimal ?_ hKall.isClosed
    intro y hy
    by_contra hyK
    exact hy (sub_eq_zero.mpr (hFfix y hyK).1)
  · apply closure_minimal ?_ hKall.isClosed
    intro y hy
    by_contra hyK
    exact hy (sub_eq_zero.mpr (hFfix y hyK).2)

end PoincareConjecture.M25.Topology3D
