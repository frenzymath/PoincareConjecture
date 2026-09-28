import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurfaceMorse
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FiniteHeightCuts
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.InitialCollarCutState
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCoreGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilySourceAtlasHistory
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilySourceMorse

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace BigOperators

namespace PoincareConjecture.M25.Topology3D

theorem exists_terminal_collar_morse_family
    (hP : PlanarSchoenfliesService)
    (original : UnitTwoSphere × ℝ → E3)
    (horiginal : IsCollarEmbedding original)
    (P : SurgeryCapProfile) :
    ∃ u : UnitTwoSphere,
      let originalHeight := fun q : UnitTwoSphere =>
        ⟪(u : E3), original (q, 0)⟫_ℝ
      let originalCritical := {q : UnitTwoSphere |
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) originalHeight q = 0}
      originalCritical.Finite ∧ InjOn originalHeight originalCritical ∧
      ∃ r : ℕ, ∃ cut : Fin r → ℝ, ∃ D : ℝ,
        0 < D ∧
        Pairwise (fun a b : Fin r =>
          Disjoint (Icc (cut a - D) (cut a + D))
            (Icc (cut b - D) (cut b + D))) ∧
        (∀ k : Fin r, ∀ q : UnitTwoSphere, originalHeight q = cut k →
          mfderiv (𝓡 2) 𝓘(ℝ, ℝ) originalHeight q ≠ 0) ∧
        (∀ p ∈ originalCritical, ∀ q ∈ originalCritical,
          originalHeight p < originalHeight q →
            ∃ k : Fin r, originalHeight p < cut k ∧ cut k < originalHeight q) ∧
        (∀ k : Fin r, ∀ q ∈ originalCritical,
          4 * D < |originalHeight q - cut k|) ∧
        ∃ m0 : Fin r → ℕ,
          ∃ B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2,
            ∃ Phi : Fin r → ℝ →
              Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞,
              ∃ n : ℕ, ∃ phi : Fin n → UnitTwoSphere × ℝ → E3,
                ∃ T : FamilyCutState P u r cut D m0 B Phi n phi,
                  ∃ _A : FamilySourceAtlas original T,
                    ∃ history : FamilySurgeryHistory u
                      (fun _ : Fin 1 => original) phi,
                      T.measure = 0 ∧ (∀ k : Fin r, T.count k = 0) ∧
                      history.length = ∑ k : Fin r, m0 k ∧
                      n = 1 + history.length ∧
                      T.capCount = 2 * history.length ∧
                      (∀ q ∈ originalCritical,
                        original (q, 0) ∈
                          (⋃ i : Fin n, range (fun p : UnitTwoSphere => phi i (p, 0)))) ∧
                      ∀ i : Fin n,
                        IsCompact (T.sourceCore i) ∧ IsConnected (T.sourceCore i) ∧
                        (T.sourceCore i ∩ {q : UnitTwoSphere |
                          mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
                            (fun p : UnitTwoSphere =>
                              ⟪(u : E3), phi i (p, 0)⟫_ℝ) q = 0}).Subsingleton ∧
                        ∀ q ∈ T.sourceCore i,
                          mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
                            (fun p : UnitTwoSphere => ⟪(u : E3), phi i (p, 0)⟫_ℝ) q = 0 →
                          ∃ (sigma tau : ℝ)
                            (e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ)),
                            sigma * sigma = 1 ∧ tau * tau = 1 ∧
                            q ∈ e.source ∧ e q = 0 ∧
                            ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source ∧
                            ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target ∧
                            ∀ p ∈ e.source,
                              ⟪(u : E3), phi i (p, 0)⟫_ℝ =
                                ⟪(u : E3), phi i (q, 0)⟫_ℝ +
                                  sigma * (e p).1 ^ 2 + tau * (e p).2 ^ 2 := by
  classical
  obtain ⟨u, hfinite, hdistinct, hmorse⟩ :=
    exists_generic_collar_morse_height original horiginal
  refine ⟨u, hfinite, hdistinct, ?_⟩
  let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), original (q, 0)⟫_ℝ
  let critical : Set UnitTwoSphere := {q | mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q = 0}
  obtain ⟨C, hC, hregular, hseparates, _hbetween⟩ :=
    exists_regular_separating_height_cuts original u hfinite
  obtain ⟨D, hD, _hsmall, hgap, hbuffers⟩ :=
    exists_separated_regular_height_buffers original u hfinite C hC hregular
      (fun _ => 1) (fun _ _ => zero_lt_one)
  let : Fintype C := hC.fintype
  let r := Fintype.card C
  let eC : Fin r ≃ C := (Fintype.equivFin C).symm
  let cut : Fin r → ℝ := fun k => (eC k).1
  have hcut (k : Fin r) : cut k ∈ C := (eC k).2
  have hcutinj : Function.Injective cut := by
    intro a b hab
    apply eC.injective
    exact Subtype.ext hab
  have hseparated : Pairwise (fun a b : Fin r =>
      Disjoint (Icc (cut a - D) (cut a + D))
        (Icc (cut b - D) (cut b + D))) := by
    intro a b hab
    exact hbuffers (cut a) (hcut a) (cut b) (hcut b) (fun h => hab (hcutinj h))
  have hreg (k : Fin r) (q : UnitTwoSphere) (hq : f q = cut k) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q ≠ 0 := hregular (cut k) (hcut k) q hq
  have hsep : ∀ p ∈ critical, ∀ q ∈ critical, f p < f q →
      ∃ k : Fin r, f p < cut k ∧ cut k < f q := by
    intro p hp q hq hpq
    obtain ⟨t, ht, hpt, htq⟩ := hseparates p hp q hq hpq
    refine ⟨eC.symm ⟨t, ht⟩, ?_, ?_⟩
    · simpa only [cut, Equiv.apply_symm_apply] using hpt
    · simpa only [cut, Equiv.apply_symm_apply] using htq
  obtain ⟨m0, B, _e, _hcomponents, _d, _hd, Phi, _hidentity, _hsupport,
      _hlevel, S, _hcount, _hwidth, hcap, _hlabels, hmeasure⟩ :=
    exists_initial_collar_cut_state hP original horiginal P u r cut D hD hseparated hreg
  obtain ⟨A, _hcore, _hA⟩ := FamilySourceAtlas.exists_initial original S hcap
  let K : Set E3 := (fun q : UnitTwoSphere => original (q, 0)) '' critical
  have hK : IsCompact K := (hfinite.image (fun q => original (q, 0))).isCompact
  have hmiss : ∀ k : Fin r, ∀ y ∈ K, ⟪(u : E3), y⟫_ℝ ≠ cut k := by
    rintro k y ⟨q, hq, rfl⟩ hy
    exact hreg k q hy hq
  obtain ⟨n, phi, T, A', history, hzero, hcounts, hlength, hsize, hcaps,
      _hwidths, _hcapmono, hpreserved⟩ := A.exists_terminal_history hP K hK hmiss
  refine ⟨r, cut, D, hD, hseparated, hreg, hsep,
    (fun k q hq => hgap (cut k) (hcut k) q hq), m0, B, Phi, n, phi, T, A',
    history, hzero, hcounts, hlength.trans hmeasure, ?_, ?_, ?_, ?_⟩
  · simpa only [hlength] using hsize
  · simpa only [hcap, zero_add, hlength] using hcaps
  · intro q hq
    apply (hpreserved (original (q, 0)) ⟨q, hq, rfl⟩).mpr
    exact mem_iUnion.mpr ⟨0, q, rfl⟩
  · intro i
    have htop := T.sourceCore_compact_connected i
    refine ⟨htop.1, htop.2,
      A'.sourceCore_critical_subsingleton horiginal hcounts hdistinct hsep i, ?_⟩
    intro q hq hqcrit
    have hqA : q ∈ (A'.chart i).source := A'.core_subset_source i hq
    have hqold := (A'.height_critical_iff horiginal i q hqA).mp hqcrit
    obtain ⟨sigma, tau, e, hsigma, htau, hqe, heq, he, hei, hform⟩ :=
      hmorse (A'.chart i q) hqold
    obtain ⟨_hsource, _htarget, _hforward, _hinverse, _hsigma, _htau,
        hqsource, hqcenter, _hzeroTarget, _hsymm, he', hei', _hcentral, hform'⟩ :=
      A'.morse_chart i (A'.chart i q) ((A'.chart i).map_source hqA)
        sigma tau e hsigma htau hqe heq he hei hform
    have hqinverse : (A'.chart i).symm (A'.chart i q) = q := (A'.chart i).left_inv hqA
    refine ⟨sigma, tau, (A'.chart i).trans e, hsigma, htau, ?_, ?_, he', hei', ?_⟩
    · simpa only [hqinverse] using hqsource
    · simpa only [hqinverse] using hqcenter
    · simpa only [hqinverse] using hform'

end PoincareConjecture.M25.Topology3D
