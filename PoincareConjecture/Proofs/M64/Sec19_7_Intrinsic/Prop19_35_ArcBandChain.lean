import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThinGraphBands

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem subgraph_slice_image (F : ℝ × ℝ → AnnulusCoordinates) (h : ℝ → ℝ)
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

theorem m64Intrinsic_exists_arc_band_chain
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma)
    {a b : ℝ} (hab : a < b) (hinj : InjOn gamma (Icc a b))
    (hregular : ∀ t ∈ Icc a b, deriv gamma t ≠ 0) :
    ∃ (n : ℕ) (c : Fin (n + 1) → ℝ)
      (L : Fin n → AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
      (G : Fin n → OpenPartialHomeomorph ℝ ℝ) (f : Fin n → ℝ → ℝ),
      0 < n ∧ StrictMono c ∧ c 0 = a ∧ c (Fin.last n) = b ∧
      ∃ epsilon > 0, ∀ r : Fin (n + 1) → ℝ, (∀ k, r k ∈ Ioo (0 : ℝ) epsilon) →
        ∃ B : ∀ i : Fin n,
          ObliqueBandFaces
            (collarParameterEquiv.trans (L i).symm).toHomeomorph.toOpenPartialHomeomorph
            (f i) (G i (c i.castSucc)) (G i (c i.succ))
            (L i (quarterTurn (deriv gamma (c i.castSucc)))).1
            (L i (quarterTurn (deriv gamma (c i.castSucc)))).2
            (L i (quarterTurn (deriv gamma (c i.succ)))).1
            (L i (quarterTurn (deriv gamma (c i.succ)))).2
            (r i.castSucc) (r i.succ),
          (∀ i, (B i).lowerArc = gamma '' Icc (c i.castSucc) (c i.succ) ∧
            (B i).leftCut = segment ℝ (gamma (c i.castSucc))
              (gamma (c i.castSucc) + r i.castSucc • quarterTurn (deriv gamma (c i.castSucc))) ∧
            (B i).rightCut = segment ℝ (gamma (c i.succ))
              (gamma (c i.succ) + r i.succ • quarterTurn (deriv gamma (c i.succ)))) ∧
          (∀ i j : Fin n, i.succ < j.castSucc → Disjoint (B i).carrier (B j).carrier) ∧
          ∀ i j : Fin n, i.succ = j.castSucc →
            (B i).carrier ∩ (B j).carrier = segment ℝ (gamma (c i.succ))
              (gamma (c i.succ) + r i.succ • quarterTurn (deriv gamma (c i.succ))) := by
  classical
  obtain ⟨n, c, L, G, f, hf, P, delta, hdelta, hn, hc, hfirst, hlast,
    hgraph, hstrip, hdisjoint, hadj⟩ :=
    m64Intrinsic_exists_separated_arc_strips hg hab hinj hregular
  let F (i : Fin n) := (P i).linearCoordinates (L i).symm (G i).open_target (hf i)
  have hstep (i : Fin n) := hc (Fin.castSucc_lt_succ (i := i))
  have ha (i : Fin n) := (hgraph i).1 (left_mem_Icc.mpr (hstep i).le)
  have hb (i : Fin n) := (hgraph i).1 (right_mem_Icc.mpr (hstep i).le)
  have hpositive (i : Fin n) := (hgraph i).2.1 (ha i) (hb i) (hstep i)
  have hbands (i : Fin n) := m64Intrinsic_exists_thin_graph_bands
    (L i).symm (G i).open_target (hf i) (hpositive i)
    (hgraph i).2.2.2.2.2 (P i) hdelta
  choose cutoff hcutoff hbands using hbands
  obtain ⟨epsilon, hepsilon, hle⟩ := exists_pos_le_finite_family cutoff hcutoff
  refine ⟨n, c, L, G, f, hn, hc, hfirst, hlast, epsilon, hepsilon, ?_⟩
  intro r hr
  have hleft (i : Fin n) : r i.castSucc ∈ Ioo (0 : ℝ) (cutoff i) :=
    ⟨(hr i.castSucc).1, (hr i.castSucc).2.trans_le (hle i)⟩
  have hright (i : Fin n) : r i.succ ∈ Ioo (0 : ℝ) (cutoff i) :=
    ⟨(hr i.succ).1, (hr i.succ).2.trans_le (hle i)⟩
  choose B hB using fun i => hbands i _ (hleft i) _ (hright i)
  have hcoordinates (i : Fin n) (q : AnnulusCoordinates) :
      (B i).coordinates q = F i (collarParameterEquiv q) := (hB i).2.2.1 q
  have hheight (i : Fin n) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (B i).height t < delta := (hB i).2.2.2.1 t ht
  have hcarrier (i : Fin n) : (B i).carrier = F i ''
      {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ (B i).height q.1} :=
    (hB i).2.2.2.2.1
  have hcuts (i : Fin n) :
      (B i).leftCut = segment ℝ (gamma (c i.castSucc))
        (gamma (c i.castSucc) + r i.castSucc • quarterTurn (deriv gamma (c i.castSucc))) ∧
      (B i).rightCut = segment ℝ (gamma (c i.succ))
        (gamma (c i.succ) + r i.succ • quarterTurn (deriv gamma (c i.succ))) := by
    constructor
    · rw [(hB i).2.2.2.2.2.1, ← (hgraph i).2.2.2.1 _ (ha i)]
      simp only [Prod.eta, (L i).symm_apply_apply]
    · rw [(hB i).2.2.2.2.2.2, ← (hgraph i).2.2.2.1 _ (hb i)]
      simp only [Prod.eta, (L i).symm_apply_apply]
  have hsub (i : Fin n) : (B i).carrier ⊆ F i '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta) := by
    rw [hcarrier]
    apply image_mono
    intro q hq
    exact ⟨hq.1, ⟨by linarith [hq.2.1], hq.2.2.trans_lt (hheight i q.1 hq.1)⟩⟩
  refine ⟨B, ?_, fun i j hij => (hdisjoint i j hij).mono (hsub i) (hsub j), ?_⟩
  · intro i
    refine ⟨?_, hcuts i⟩
    change (fun x => (L i).symm
      (collarParameterEquiv (collarParameterEquiv.symm (x, f i x)))) ''
        Icc (G i (c i.castSucc)) (G i (c i.succ)) = _
    simp only [collarParameterEquiv.apply_symm_apply]
    rw [← (hgraph i).2.2.2.2.1, image_image]
    exact image_congr (fun t ht => by
      rw [← (hgraph i).2.2.2.1 t ((hgraph i).1 ht), (L i).symm_apply_apply])
  · intro i j hij
    rw [hcarrier, hcarrier]
    apply image_inter_eq_of_endpoint_separation
    · intro q hq u hu heq
      apply hadj i j hij q.1 hq.1 u.1 hu.1 q.2 u.2
      · rw [abs_of_nonneg hq.2.1]
        exact hq.2.2.trans_lt (hheight i q.1 hq.1)
      · rw [abs_of_nonneg hu.2.1]
        exact hu.2.2.trans_lt (hheight j u.1 hu.1)
      · exact heq
    · rw [subgraph_slice_image _ _ (by simp)]
      rw [← (hcuts i).2, ← (B i).right_height_image]
      apply image_congr
      intro z _
      rw [hcoordinates, collarParameterEquiv.apply_symm_apply]
    · rw [subgraph_slice_image _ _ (by simp)]
      have hcut : (B j).leftCut = segment ℝ (gamma (c i.succ))
          (gamma (c i.succ) + r i.succ • quarterTurn (deriv gamma (c i.succ))) := by
        rw [hij]
        exact (hcuts j).1
      rw [← hcut, ← (B j).left_height_image]
      apply image_congr
      intro z _
      rw [hcoordinates, collarParameterEquiv.apply_symm_apply]

end PoincareConjecture
