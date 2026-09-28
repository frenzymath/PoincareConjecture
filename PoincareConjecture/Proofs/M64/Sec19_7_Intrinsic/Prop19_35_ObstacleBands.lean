import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapAvoidingReturnStrips
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_InwardTransverseBands













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem slice_image (F : ℝ × ℝ → AnnulusCoordinates) (h : ℝ → ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    F '' ({q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ h q.1} ∩
      {q | q.1 = t}) = (fun z => F (t, z)) '' Icc (0 : ℝ) (h t) := by
  ext p
  constructor
  · rintro ⟨⟨s, z⟩, ⟨⟨hs, hz⟩, hst⟩, heq⟩
    change s = t at hst
    subst s
    exact ⟨z, hz, heq⟩
  · rintro ⟨z, hz, heq⟩
    exact ⟨(t, z), ⟨⟨ht, hz⟩, rfl⟩, heq⟩





theorem m64Intrinsic_exists_inward_obstacle_band_chain
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T a b : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (ha : 0 < a) (hb : b < T)
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    {U : Set AnnulusCoordinates} (hU : IsOpen U)
    (hfront : frontier U = gamma '' Icc 0 T)
    (hray : ∀ t ∈ Ioo (0 : ℝ) T, ∀ᶠ z in 𝓝[>] (0 : ℝ),
      gamma t + z • quarterTurn (deriv gamma t) ∈ U)
    (d : ℝ → AnnulusCoordinates)
    (hd : ∀ t ∈ Icc a b, 0 < inner ℝ (quarterTurn (deriv gamma t)) (d t))
    {C : Set AnnulusCoordinates}
    (hpaths : ∀ z ∈ Icc (0 : ℝ) 1,
      gamma a + z • d a ∈ C ∧ gamma b + z • d b ∈ C)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (L : Fin n → AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (G : Fin n → OpenPartialHomeomorph ℝ ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (G i).target)
    (P : ∀ i, TransverseGraphCuts (f i) (G i (c i.castSucc)) (G i (c i.succ))
      (L i (d (c i.castSucc))).1 (L i (d (c i.castSucc))).2
      (L i (d (c i.succ))).1 (L i (d (c i.succ))).2)
    (hc : StrictMono c) (hfirst : c 0 = a) (hlast : c (Fin.last n) = b)
    (hgraph : ∀ i, Icc (c i.castSucc) (c i.succ) ⊆ (G i).source ∧
      StrictMonoOn (G i) (G i).source ∧ ContDiffOn ℝ ∞ (G i) (G i).source ∧
      (∀ t ∈ (G i).source, L i (gamma t) = (G i t, f i (G i t))) ∧
      G i '' Icc (c i.castSucc) (c i.succ) =
        Icc (G i (c i.castSucc)) (G i (c i.succ)) ∧
      Icc (G i (c i.castSucc)) (G i (c i.succ)) ⊆ (G i).target)
    {rho : ℝ} (hrho : 0 < rho) :
    let S (i : Fin n) := (P i).linearCoordinates (L i).symm (G i).open_target (hf i)
    (∀ i, (fun t => S i (t, 0)) '' Icc (0 : ℝ) 1 =
      gamma '' Icc (c i.castSucc) (c i.succ)) →
    (∀ i j : Fin n, i.succ < j.castSucc →
      Disjoint (S i '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-rho) rho))
        (S j '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-rho) rho))) →
    (∀ i j : Fin n, i.succ = j.castSucc →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ z w : ℝ, |z| < rho → |w| < rho →
        S i (t, z) = S j (s, w) → t = 1 ∧ s = 0) →
    (∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, |z| < rho → S i (t, z) ∈ C →
      (c i.castSucc = a ∧ t = 0) ∨ (c i.succ = b ∧ t = 1)) →
    ∃ epsilon > 0, epsilon ≤ 1 ∧
      ∀ r : Fin (n + 1) → ℝ, (∀ k, r k ∈ Ioo (0 : ℝ) epsilon) →
        ∃ B : ∀ i : Fin n,
          ObliqueBandFaces
            (collarParameterEquiv.trans (L i).symm).toHomeomorph.toOpenPartialHomeomorph
            (f i) (G i (c i.castSucc)) (G i (c i.succ))
            (L i (d (c i.castSucc))).1 (L i (d (c i.castSucc))).2
            (L i (d (c i.succ))).1 (L i (d (c i.succ))).2
            (r i.castSucc) (r i.succ),
          (∀ i, (B i).lowerArc = gamma '' Icc (c i.castSucc) (c i.succ) ∧
            (B i).leftCut = segment ℝ (gamma (c i.castSucc))
              (gamma (c i.castSucc) + r i.castSucc • d (c i.castSucc)) ∧
            (B i).rightCut = segment ℝ (gamma (c i.succ))
              (gamma (c i.succ) + r i.succ • d (c i.succ)) ∧
            (B i).carrier ⊆ closure U ∧ (B i).carrier \ (B i).lowerArc ⊆ U) ∧
          (∀ i j : Fin n, i.succ < j.castSucc → Disjoint (B i).carrier (B j).carrier) ∧
          (∀ i j : Fin n, i.succ = j.castSucc →
            (B i).carrier ∩ (B j).carrier = segment ℝ (gamma (c i.succ))
              (gamma (c i.succ) + r i.succ • d (c i.succ))) ∧
          ∀ i, C ∩ (B i).carrier =
            (if c i.castSucc = a then (B i).leftCut else ∅) ∪
              (if c i.succ = b then (B i).rightCut else ∅) := by
  classical
  intro S haxis hdisjoint hadj hobstacle
  have hstep (i : Fin n) := hc (Fin.castSucc_lt_succ (i := i))
  have hcut (k : Fin (n + 1)) : c k ∈ Icc a b := by
    constructor
    · simpa only [hfirst] using hc.monotone (Fin.zero_le k)
    · simpa only [hlast] using hc.monotone (Fin.le_last k)
  have hleft (i : Fin n) := (hgraph i).1 (left_mem_Icc.mpr (hstep i).le)
  have hright (i : Fin n) := (hgraph i).1 (right_mem_Icc.mpr (hstep i).le)
  have hinward (i : Fin n) : ∃ s > 0,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) s,
        (t, z) ∈ (S i).source ∧ S i (t, z) ∈ closure U ∧
          (0 < z → S i (t, z) ∈ U) := by
    apply m64Intrinsic_exists_inward_graph_strip hg.continuous hend hinj (hstep i)
      (ha.trans_le (hcut i.castSucc).1) ((hcut i.succ).2.trans_lt hb) hU hfront
      (L i) (G i) (hf i) (hgraph i).1 (hgraph i).2.1 (hgraph i).2.2.2.1
      (hgraph i).2.2.2.2.1 (hgraph i).2.2.2.2.2 (P i)
    simpa only [Prod.eta, (L i).symm_apply_apply] using
      m64Intrinsic_transverse_ray_enters_region hg hend hinj hregular hU hfront hray
        ⟨ha.trans_le (hcut i.castSucc).1, (hcut i.castSucc).2.trans_lt hb⟩
        (hd _ (hcut i.castSucc))
  choose width hwidth hregion using hinward
  obtain ⟨eta, heta, hetale⟩ := exists_pos_le_finite_family width hwidth
  let delta := min rho eta
  have hdelta : 0 < delta := lt_min hrho heta
  have hdr : delta ≤ rho := min_le_left _ _
  have hdw (i : Fin n) : delta ≤ width i := (min_le_right _ _).trans (hetale i)
  have hpositive (i : Fin n) := (hgraph i).2.1 (hleft i) (hright i) (hstep i)
  have hbands (i : Fin n) := m64Intrinsic_exists_thin_graph_bands
    (L i).symm (G i).open_target (hf i) (hpositive i)
    (hgraph i).2.2.2.2.2 (P i) hdelta
  choose cutoff hcutoff hbands using hbands
  obtain ⟨epsilon, hepsilon, hle⟩ := exists_pos_le_finite_family cutoff hcutoff
  refine ⟨min epsilon 1, lt_min hepsilon zero_lt_one, min_le_right _ _, ?_⟩
  intro r hr
  have hrle (k : Fin (n + 1)) : r k ≤ 1 :=
    ((hr k).2.trans_le (min_le_right _ _)).le
  choose B hB using fun i => hbands i (r i.castSucc)
    ⟨(hr i.castSucc).1, (hr i.castSucc).2.trans_le ((min_le_left _ _).trans (hle i))⟩
    (r i.succ)
    ⟨(hr i.succ).1, (hr i.succ).2.trans_le ((min_le_left _ _).trans (hle i))⟩
  have hcoordinates (i : Fin n) (q : AnnulusCoordinates) :
      (B i).coordinates q = S i (collarParameterEquiv q) := (hB i).2.2.1 q
  have hheight (i : Fin n) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (B i).height t < delta := (hB i).2.2.2.1 t ht
  have hcarrier (i : Fin n) : (B i).carrier = S i ''
      {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ (B i).height q.1} :=
    (hB i).2.2.2.2.1
  have hbottom (i : Fin n) : (B i).lowerArc = gamma '' Icc (c i.castSucc) (c i.succ) := by
    change (fun x => (L i).symm
      (collarParameterEquiv (collarParameterEquiv.symm (x, f i x)))) ''
        Icc (G i (c i.castSucc)) (G i (c i.succ)) = _
    simp only [collarParameterEquiv.apply_symm_apply]
    rw [← (hgraph i).2.2.2.2.1, image_image]
    exact image_congr (fun t ht => by
      rw [← (hgraph i).2.2.2.1 t ((hgraph i).1 ht), (L i).symm_apply_apply])
  have hcuts (i : Fin n) :
      (B i).leftCut = segment ℝ (gamma (c i.castSucc))
        (gamma (c i.castSucc) + r i.castSucc • d (c i.castSucc)) ∧
      (B i).rightCut = segment ℝ (gamma (c i.succ))
        (gamma (c i.succ) + r i.succ • d (c i.succ)) := by
    constructor
    · rw [(hB i).2.2.2.2.2.1, ← (hgraph i).2.2.2.1 _ (hleft i)]
      simp only [Prod.eta, (L i).symm_apply_apply]
    · rw [(hB i).2.2.2.2.2.2, ← (hgraph i).2.2.2.1 _ (hright i)]
      simp only [Prod.eta, (L i).symm_apply_apply]
  have hcutImages (i : Fin n) :
      (fun z => S i (0, z)) '' Icc (0 : ℝ) ((B i).height 0) = (B i).leftCut ∧
      (fun z => S i (1, z)) '' Icc (0 : ℝ) ((B i).height 1) = (B i).rightCut := by
    constructor
    · rw [← (B i).left_height_image]
      exact image_congr (fun z _ => by
        rw [hcoordinates, collarParameterEquiv.apply_symm_apply])
    · rw [← (B i).right_height_image]
      exact image_congr (fun z _ => by
        rw [hcoordinates, collarParameterEquiv.apply_symm_apply])
  have hcutCarrier (i : Fin n) :
      (B i).leftCut ⊆ (B i).carrier ∧ (B i).rightCut ⊆ (B i).carrier := by
    rw [← (hcutImages i).1, ← (hcutImages i).2, hcarrier]
    constructor
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨(0, z), ⟨by simp, hz⟩, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨(1, z), ⟨by simp, hz⟩, rfl⟩
  have hsub (i : Fin n) : (B i).carrier ⊆ S i '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-rho) rho) := by
    rw [hcarrier]
    apply image_mono
    intro q hq
    exact ⟨hq.1, ⟨by linarith [hq.2.1], (hq.2.2.trans_lt (hheight i q.1 hq.1)).trans_le hdr⟩⟩
  refine ⟨B, ?_, fun i j hij => (hdisjoint i j hij).mono (hsub i) (hsub j), ?_, ?_⟩
  · intro i
    refine ⟨hbottom i, (hcuts i).1, (hcuts i).2, ?_, ?_⟩
    · rw [hcarrier]
      rintro _ ⟨q, hq, rfl⟩
      exact (hregion i q.1 hq.1 q.2
        ⟨hq.2.1, (hq.2.2.trans_lt (hheight i q.1 hq.1)).le.trans (hdw i)⟩).2.1
    · rintro p ⟨hp, hpnot⟩
      rw [hcarrier] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      have hqpos : 0 < q.2 := by
        by_contra hn
        have hz : q.2 = 0 := le_antisymm (le_of_not_gt hn) hq.2.1
        apply hpnot
        rw [hbottom, ← haxis]
        exact ⟨q.1, hq.1, by rw [← hz]⟩
      exact (hregion i q.1 hq.1 q.2
        ⟨hq.2.1, (hq.2.2.trans_lt (hheight i q.1 hq.1)).le.trans (hdw i)⟩).2.2 hqpos
  · intro i j hij
    rw [hcarrier, hcarrier]
    apply image_inter_eq_of_endpoint_separation
    · intro q hq u hu heq
      exact hadj i j hij q.1 hq.1 u.1 hu.1 q.2 u.2
        (by rw [abs_of_nonneg hq.2.1]
            exact (hq.2.2.trans_lt (hheight i q.1 hq.1)).trans_le hdr)
        (by rw [abs_of_nonneg hu.2.1]
            exact (hu.2.2.trans_lt (hheight j u.1 hu.1)).trans_le hdr) heq
    · rw [slice_image _ _ (by simp), (hcutImages i).2, (hcuts i).2]
    · rw [slice_image _ _ (by simp), (hcutImages j).1, (hcuts j).1, hij]
  · intro i
    ext p
    constructor
    · rintro ⟨hpC, hp⟩
      rw [hcarrier] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      have hqwidth : |q.2| < rho := by
        rw [abs_of_nonneg hq.2.1]
        exact (hq.2.2.trans_lt (hheight i q.1 hq.1)).trans_le hdr
      rcases hobstacle i q.1 hq.1 q.2 hqwidth hpC with ⟨hi, ht⟩ | ⟨hi, ht⟩
      · apply Or.inl
        rw [if_pos hi, ← (hcutImages i).1]
        exact ⟨q.2, by simpa only [mem_Icc, ht] using hq.2, by rw [← ht]⟩
      · apply Or.inr
        rw [if_pos hi, ← (hcutImages i).2]
        exact ⟨q.2, by simpa only [mem_Icc, ht] using hq.2, by rw [← ht]⟩
    · intro hp
      rcases hp with hp | hp
      · split_ifs at hp with hi
        · refine ⟨?_, (hcutCarrier i).1 hp⟩
          rw [(hcuts i).1, hi, segment_eq_image] at hp
          obtain ⟨z, hz, rfl⟩ := hp
          have hz' : z * r i.castSucc ∈ Icc (0 : ℝ) 1 :=
            ⟨mul_nonneg hz.1 (hr i.castSucc).1.le,
              (mul_le_mul_of_nonneg_right hz.2 (hr i.castSucc).1.le).trans
                (by simpa only [one_mul] using hrle i.castSucc)⟩
          convert (hpaths _ hz').1 using 1
          module
        · exact hp.elim
      · split_ifs at hp with hi
        · refine ⟨?_, (hcutCarrier i).2 hp⟩
          rw [(hcuts i).2, hi, segment_eq_image] at hp
          obtain ⟨z, hz, rfl⟩ := hp
          have hz' : z * r i.succ ∈ Icc (0 : ℝ) 1 :=
            ⟨mul_nonneg hz.1 (hr i.succ).1.le,
              (mul_le_mul_of_nonneg_right hz.2 (hr i.succ).1.le).trans
                (by simpa only [one_mul] using hrle i.succ)⟩
          convert (hpaths _ hz').2 using 1
          module
        · exact hp.elim

end PoincareConjecture
