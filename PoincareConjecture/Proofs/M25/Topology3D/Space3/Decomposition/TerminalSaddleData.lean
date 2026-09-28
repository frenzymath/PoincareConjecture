import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCoreGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyCutSides
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.ExtremumCoreProtection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PieceData











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D



theorem FamilySourceAtlas.exists_saddle_piece_data
    {original : UnitTwoSphere × ℝ → E3}
    {P : SurgeryCapProfile} {u : UnitTwoSphere}
    {r : ℕ} {cut : Fin r → ℝ} {D : ℝ}
    {m0 : Fin r → ℕ}
    {B : (k : Fin r) → Fin (m0 k) → BallNeighborhoodChart E2 E2}
    {Phi : Fin r → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞}
    {n : ℕ} {psi : Fin n → UnitTwoSphere × ℝ → E3}
    {S : FamilyCutState P u r cut D m0 B Phi n psi}
    (atlas : FamilySourceAtlas original S)
    (horiginal : IsCollarEmbedding original)
    (hzero : ∀ k : Fin r, S.count k = 0)
    (hgap : ∀ k : Fin r, ∀ p : UnitTwoSphere,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun x : UnitTwoSphere => ⟪(u : E3), original (x, 0)⟫_ℝ) p = 0 →
      4 * D < |⟪(u : E3), original (p, 0)⟫_ℝ - cut k|)
    (i : Fin n) (q : UnitTwoSphere) (hqCore : q ∈ S.sourceCore i)
    (hqCritical : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p : UnitTwoSphere => ⟪(u : E3), psi i (p, 0)⟫_ℝ) q = 0)
    (hunique : ∀ p ∈ S.sourceCore i,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun x : UnitTwoSphere => ⟪(u : E3), psi i (x, 0)⟫_ℝ) p = 0 → p = q)
    (e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ))
    (hqe : q ∈ e.source) (heq : e q = 0)
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    (sigma tau : ℝ) (hsigma : sigma * sigma = 1) (hopposite : tau = -sigma)
    (hform : ∀ p ∈ e.source,
      ⟪(u : E3), psi i (p, 0)⟫_ℝ = ⟪(u : E3), psi i (q, 0)⟫_ℝ +
        sigma * (e p).1 ^ 2 + tau * (e p).2 ^ 2) :
    ∃ piece : SaddlePieceData (psi i) u,
      piece.sourceCore = S.sourceCore i ∧ piece.point = q ∧ piece.morse = e ∧
      piece.morseSign1 = sigma ∧ piece.morseSign2 = tau ∧
      piece.capCount = Fintype.card {a : Fin S.capCount // S.owner a = i} ∧
      (∀ a : Fin piece.capCount, piece.cutRadius a = 2 * D) ∧
      ∃ labels : Fin piece.capCount ≃ {a : Fin S.capCount // S.owner a = i},
        ∀ a : Fin piece.capCount,
          piece.cap a = Eq.mp
            (congrArg (fun j : Fin n => SurgeryCapTag (psi j) u) (labels a).property)
            (S.cap (labels a).val) := by
  classical
  let I := {a : Fin S.capCount // S.owner a = i}
  let N := Fintype.card I
  let labels : Fin N ≃ I := (Fintype.equivFin I).symm
  let C : Fin N → SurgeryCapTag (psi i) u := fun a =>
    Eq.mp (congrArg (fun j : Fin n => SurgeryCapTag (psi j) u) (labels a).property)
      (S.cap (labels a).val)
  have htransport (j k : Fin n) (h : j = k) (T : SurgeryCapTag (psi j) u) :
      let T' := Eq.mp (congrArg (fun l : Fin n => SurgeryCapTag (psi l) u) h) T
      T'.sourceCap = T.sourceCap ∧ T'.sourceSeam = T.sourceSeam ∧
        T'.cap = T.cap ∧ T'.cutHeight = T.cutHeight ∧
        T'.removal = T.removal ∧ T'.sign = T.sign := by
    subst k
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hfields (a : Fin N) := htransport _ _ (labels a).property (S.cap (labels a).val)
  have hCsource (a : Fin N) : (C a).sourceCap = (S.cap (labels a).val).sourceCap :=
    (hfields a).1
  have hCseam (a : Fin N) : (C a).sourceSeam = (S.cap (labels a).val).sourceSeam :=
    (hfields a).2.1
  have hCcap (a : Fin N) : (C a).cap = (S.cap (labels a).val).cap :=
    (hfields a).2.2.1
  have hCcut (a : Fin N) : (C a).cutHeight = (S.cap (labels a).val).cutHeight :=
    (hfields a).2.2.2.1
  have hCremoval (a : Fin N) : (C a).removal = (S.cap (labels a).val).removal :=
    (hfields a).2.2.2.2.1
  have hCsign (a : Fin N) : (C a).sign = (S.cap (labels a).val).sign :=
    (hfields a).2.2.2.2.2
  have hcover : S.sourceCore i ∪ (⋃ a, (C a).sourceCap) = univ := by
    apply subset_antisymm (subset_univ _)
    intro p _hp
    by_cases hp : p ∈ S.sourceCore i
    · exact Or.inl hp
    · have hU : p ∈ ⋃ a : I, (S.cap a.val).sourceCapInterior := by
        by_contra hn
        exact hp ⟨mem_univ _, hn⟩
      obtain ⟨a, ha⟩ := mem_iUnion.mp hU
      apply Or.inr
      apply mem_iUnion.mpr
      refine ⟨labels.symm a, ?_⟩
      rw [hCsource, labels.apply_symm_apply]
      exact (S.cap a.val).sourceCapInterior_subset ha
  have hincidence (a : Fin N) :
      S.sourceCore i ∩ (C a).sourceCap = (C a).sourceSeam := by
    rw [hCsource, hCseam, inter_comm]
    simpa only [(labels a).property] using
      S.sourceCore_mem_and_seams.2 (labels a).val
  have hdisjoint (a b : Fin N) (hab : a ≠ b) :
      Disjoint (C a).sourceCap (C b).sourceCap := by
    apply disjoint_left.mpr
    intro p hpa hpb
    have hindices : (labels a).val ≠ (labels b).val := by
      intro h
      exact hab (labels.injective (Subtype.ext h))
    apply disjoint_left.mp (S.caps_disjoint hindices)
    · rw [← hCcap a]
      exact ⟨p, hpa, rfl⟩
    · rw [← hCcap b]
      exact ⟨p, hpb, rfl⟩
  let f : UnitTwoSphere → ℝ := fun p => ⟪(u : E3), psi i (p, 0)⟫_ℝ
  have hf : Continuous f :=
    continuous_const.inner (collar_central_contMDiff (psi i) (S.embedding i)).continuous
  obtain ⟨hcompact, hconnected⟩ := S.sourceCore_compact_connected i
  obtain ⟨pmin, _hpmin, hmin⟩ := hcompact.exists_isMinOn ⟨q, hqCore⟩ hf.continuousOn
  obtain ⟨pmax, _hpmax, hmax⟩ := hcompact.exists_isMaxOn ⟨q, hqCore⟩ hf.continuousOn
  let U : Set UnitTwoSphere := (atlas.chart i).source ∩
    (fun p : UnitTwoSphere => psi i (p, 0)) ⁻¹'
      {y : E3 | ∀ k : Fin r, 2 * D < |⟪(u : E3), y⟫_ℝ - cut k|}
  obtain ⟨_hW, hU, hqU, hUcore, _havoid⟩ :=
    atlas.critical_protected_neighborhood horiginal hgap i q hqCore hqCritical
  change IsOpen U at hU
  change q ∈ U at hqU
  change U ⊆ S.sourceCore i at hUcore
  have hUi : U ⊆ interior (S.sourceCore i) := hU.subset_interior_iff.mpr hUcore
  obtain ⟨eps, heps, hball⟩ :=
    Metric.isOpen_iff.mp (e.open_source.inter hU) q ⟨hqe, hqU⟩
  have hprotected : closure (ball q (eps / 2)) ⊆ e.source ∩ interior (S.sourceCore i) := by
    intro p hp
    have hin := hball ((closedBall_subset_ball (by linarith only [heps]))
      (closure_ball_subset_closedBall hp))
    exact ⟨hin.1, hUi hin.2⟩
  have hqSource := atlas.core_subset_source i hqCore
  have hcritOriginal := (atlas.height_critical_iff horiginal i q hqSource).mp hqCritical
  have hcentral : psi i (q, 0) = original (atlas.chart i q, 0) := by
    simpa only [mul_zero] using atlas.collar_eq i q hqSource 0 (by norm_num)
  have hgapCurrent (k : Fin r) : 4 * D < |f q - cut k| := by
    have hg := hgap k (atlas.chart i q) hcritOriginal
    rw [← hcentral] at hg
    exact hg
  have hremoval (a : Fin N) : (C a).removal < 2 * D := by
    rw [hCremoval]
    linarith only [S.cap_removal (labels a).val, S.buffer_pos]
  have hcutgap (a : Fin N) : 2 * D < |(C a).cutHeight - f q| := by
    rw [hCcut, S.cap_cut, abs_sub_comm]
    linarith only [hgapCurrent (S.birth (labels a).val), S.buffer_pos]
  have hside (a : Fin N) :
      ((C a).sign = 1 ∧ (C a).cutHeight < f q) ∨
        ((C a).sign = -1 ∧ f q < (C a).cutHeight) := by
    rw [hCsign, hCcut]
    rcases S.cap_points_on_birth_side (labels a).val (hzero _) with ⟨hs, hh⟩ | ⟨hs, hh⟩
    · exact Or.inl ⟨hs, by simpa only [(labels a).property] using hh q⟩
    · exact Or.inr ⟨hs, by simpa only [(labels a).property] using hh q⟩
  let piece : SaddlePieceData (psi i) u := {
    capCount := N
    cap := C
    sourceCore := S.sourceCore i
    sourceCore_compact := hcompact
    sourceCore_connected := hconnected
    source_cover := hcover
    source_incidence := hincidence
    sourceCap_disjoint := hdisjoint
    point := q
    slabLower := f pmin - 1
    slabUpper := f pmax + 1
    core_in_slab := by
      rintro _ ⟨p, hp, rfl⟩
      change f pmin - 1 ≤ f p ∧ f p ≤ f pmax + 1
      have hl : f pmin ≤ f p := hmin hp
      have hu : f p ≤ f pmax := hmax hp
      constructor <;> linarith only [hl, hu]
    point_in_slab := by
      change f pmin - 1 < f q ∧ f q < f pmax + 1
      have hl : f pmin ≤ f q := hmin hqCore
      have hu : f q ≤ f pmax := hmax hqCore
      constructor <;> linarith only [hl, hu]
    unique_critical := by
      intro p hp
      constructor
      · exact hunique p hp
      · rintro rfl
        exact hqCritical
    morse := e
    morse_smooth := he
    morse_inverse := hei
    morse_point := heq
    morseSign1 := sigma
    morseSign2 := tau
    morseSign1_sq := hsigma
    morseSigns_opposite := hopposite
    morse_height := hform
    protectedSet := ball q (eps / 2)
    protected_open := isOpen_ball
    point_mem_protected := mem_ball_self (by linarith only [heps])
    protected_closure := hprotected
    cutRadius := fun _ => 2 * D
    removal_lt_cutRadius := hremoval
    cutRadius_lt_gap := hcutgap
    cut_side := hside }
  exact ⟨piece, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, labels, fun _ => rfl⟩

end PoincareConjecture.M25.Topology3D
