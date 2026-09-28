import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PieceData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.AmbientMorseChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CapCompressionBuffers
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.MorseRadialChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalBandField












set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D



theorem exists_raw_saddle_piece_band_input
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u) :
    let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let f : UnitTwoSphere → ℝ := fun q => H (j q)
    let c : ℝ := f D.point
    let S : Set E3 := range j
    let L := heightPlaneCoordinates u
    let pi := horizontalBandProjection u
    let Q : ℝ × ℝ → ℝ := fun s =>
      D.morseSign1 * s.1 ^ 2 + D.morseSign2 * s.2 ^ 2
    let B : ℝ → Set (ℝ × ℝ) := fun r => {s | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2}
    let Do : ℝ → Set (ℝ × ℝ) := fun r => {s | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}
    ∃ (R b : ℝ) (P : OpenPartialHomeomorph (ℝ × ℝ) E2)
      (A : OpenPartialHomeomorph ((ℝ × ℝ) × ℝ) E3),
      0 < R ∧ 0 < b ∧
      P.source = Do (2 * R) ∧
      A.source = Do (2 * R) ×ˢ Ioo (c - 8 * b) (c + 8 * b) ∧
      ContDiffOn ℝ ∞ P P.source ∧ ContDiffOn ℝ ∞ P.symm P.target ∧
      ContDiffOn ℝ ∞ A A.source ∧ ContDiffOn ℝ ∞ A.symm A.target ∧
      P.source ⊆ D.morse.target ∧
      (∀ s ∈ P.source, D.morse.symm s ∈ D.protectedSet ∧
        P s = pi (j (D.morse.symm s))) ∧
      P 0 = pi (j D.point) ∧ A (0, c) = j D.point ∧
      A.target = L.symm '' (P.target ×ˢ Ioo (c - 8 * b) (c + 8 * b)) ∧
      (∀ w ∈ A.source, A w = L.symm (P w.1, w.2) ∧ H (A w) = w.2 ∧
        (A w ∈ S ↔ w.2 = c + Q w.1)) ∧
      (∀ y ∈ A.target, A.symm y = (P.symm (pi y), H y)) ∧
      B R ⊆ P.source ∧ B R ×ˢ Icc (c - 4 * b) (c + 4 * b) ⊆ A.source ∧
      (∀ s ∈ B R, ∀ z : ℝ, |z - c| ≤ 4 * b →
        A (s, z) = L.symm (P s, z) ∧
        A.symm (L.symm (P s, z)) = (s, z)) ∧
      (∀ i : Fin D.capCount, ∀ y ∈ (D.cap i).cap, 8 * b < |H y - c|) ∧
      (∀ q : UnitTwoSphere, |f q - c| ≤ 8 * b → q ∈ D.sourceCore) ∧
      (∀ q : UnitTwoSphere, |f q - c| ≤ 2 * b →
        pi (j q) ∉ P '' Do (R / 4) → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q ≠ 0) := by
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let f : UnitTwoSphere → ℝ := fun q => H (j q)
  let c := f D.point
  let S := range j
  let L := heightPlaneCoordinates u
  let pi := horizontalBandProjection u
  let Q : ℝ × ℝ → ℝ := fun s => D.morseSign1 * s.1 ^ 2 + D.morseSign2 * s.2 ^ 2
  let B : ℝ → Set (ℝ × ℝ) := fun r => {s | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2}
  let Do : ℝ → Set (ℝ × ℝ) := fun r => {s | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}
  have hp := D.protected_closure (subset_closure D.point_mem_protected)
  have hpCore : D.point ∈ D.sourceCore := interior_subset hp.2
  have hpCrit := (D.unique_critical D.point hpCore).mpr rfl
  obtain ⟨T, hpT, hTsub, hTform, hTs, hTi⟩ :=
    exists_collar_critical_horizontal_chart psi hpsi u D.point hpCrit
      D.protected_open D.point_mem_protected
  let P0 := D.morse.symm.trans T
  have h0e : (0 : ℝ × ℝ) ∈ D.morse.target :=
    D.morse_point ▸ D.morse.map_source hp.1
  have he0 : D.morse.symm 0 = D.point := by
    rw [← D.morse_point, D.morse.left_inv hp.1]
  have h0P : (0 : ℝ × ℝ) ∈ P0.source := by
    refine ⟨h0e, ?_⟩
    change D.morse.symm 0 ∈ T.source
    rw [he0]
    exact hpT
  have hP0s : ContDiffOn ℝ ∞ P0 P0.source :=
    (hTs.comp (D.morse_inverse.mono inter_subset_left) (fun _ hs => hs.2)).contDiffOn
  have hP0i : ContDiffOn ℝ ∞ P0.symm P0.target :=
    (D.morse_smooth.comp (hTi.mono inter_subset_left) (fun _ hs => hs.2)).contDiffOn
  have hP0form (s : ℝ × ℝ) (hs : s ∈ P0.source) :
      D.morse.symm s ∈ D.protectedSet ∧ P0 s = pi (j (D.morse.symm s)) :=
    ⟨hTsub hs.2, hTform hs.2⟩
  have hP00 : P0 0 = pi (j D.point) := by rw [(hP0form 0 h0P).2, he0]
  obtain ⟨A0, h0A, hA0s, hA0i, hA0form⟩ :=
    exists_collar_ambient_morse_chart psi hpsi u D.point hpCrit D.morse hp.1
      D.morse_point D.morse_smooth D.morse_inverse D.morseSign1 D.morseSign2 D.morse_height
  obtain ⟨o, w, Rcap, hbuf, hsets⟩ := exists_finite_surgeryCap_compression_buffers
    psi hpsi u c D.capCount D.cap D.cutRadius D.removal_lt_cutRadius D.cutRadius_lt_gap
  let J : Set ℝ := ⋃ i, closedBall (D.cap i).cutHeight (Rcap i)
  rcases hsets with ⟨hJ, hcJ, _, _, htracks⟩
  have hcapJ (i : Fin D.capCount) (y : E3) (hy : y ∈ (D.cap i).cap) : H y ∈ J := by
    rw [(D.cap i).cap_eq_image] at hy
    rcases hy with ⟨q, hq, rfl⟩
    have ho := (hbuf i).1
    change (heightCoordinates (q : E3)).2 ≤ 0 at hq
    have hnative : (heightCoordinates (q : E3)).2 ≤ 2 * o i := by linarith
    have hsource : ((D.cap i).profile.model q).1 ∈ closedBall (0 : E2) 1 := by
      simpa only [mem_closedBall, dist_zero_right] using (D.cap i).profile.model_fst_norm_le q
    change ⟪(u : E3), _⟫_ℝ ∈ J
    rw [SurgeryCapProfile.capMap_apply, (D.cap i).tube_height
      (((D.cap i).profile.model q).1, (D.cap i).cutHeight + (D.cap i).sign *
        ((D.cap i).removal + (D.cap i).scale * ((D.cap i).profile.model q).2))
      ((D.cap i).tube_source ⟨hsource, mem_univ _⟩)]
    exact ((htracks i).2.2.1 q hnative).1
  obtain ⟨gamma, hgamma, hgammaJ⟩ := Metric.isOpen_iff.mp
    hJ.isClosed.isOpen_compl c hcJ
  have hgap (i : Fin D.capCount) (y : E3) (hy : y ∈ (D.cap i).cap) :
      gamma ≤ |H y - c| := by
    by_contra hg
    have hyball : H y ∈ ball c gamma := by
      simpa only [mem_ball, Real.dist_eq] using lt_of_not_ge hg
    exact hgammaJ hyball (hcapJ i y hy)
  let W := A0.source ∩ Prod.fst ⁻¹' P0.source
  have hW : IsOpen W := A0.open_source.inter (P0.open_source.preimage continuous_fst)
  have h0W : ((0 : ℝ × ℝ), c) ∈ W := ⟨h0A, h0P⟩
  obtain ⟨rho, hrho, hrhoW⟩ := Metric.isOpen_iff.mp hW (0, c) h0W
  let R := rho / 4
  let b := min (rho / 64) (gamma / 16)
  have hR : 0 < R := by dsimp [R]; positivity
  have hb : 0 < b := lt_min (by positivity) (by positivity)
  have hbR : b ≤ rho / 64 := min_le_left _ _
  have hbg : b ≤ gamma / 16 := min_le_right _ _
  have hDo : IsOpen (Do (2 * R)) :=
    (morseRadialDisc_geometry (2 * R) (by positivity)).1
  let U := Do (2 * R) ×ˢ Ioo (c - 8 * b) (c + 8 * b)
  have hU : IsOpen U := hDo.prod isOpen_Ioo
  have hUW : U ⊆ W := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    apply hrhoW
    have hs' : s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2 := hs
    have hsnorm : ‖s‖ < 2 * R := by
      rw [Prod.norm_def, max_lt_iff, Real.norm_eq_abs, Real.norm_eq_abs]
      constructor
      · apply (sq_lt_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * R)).mp
        rw [sq_abs]
        nlinarith [sq_nonneg s.2]
      · apply (sq_lt_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * R)).mp
        rw [sq_abs]
        nlinarith [sq_nonneg s.1]
    change max (dist s 0) (dist z c) < rho
    rw [dist_zero_right, Real.dist_eq, max_lt_iff]
    refine ⟨hsnorm.trans ?_, abs_lt.mpr ⟨?_, ?_⟩⟩
    · dsimp [R]
      linarith
    · linarith [hz.1]
    · linarith [hz.2]
  have hDoP : Do (2 * R) ⊆ P0.source := by
    intro s hs
    exact (hUW (show (s, c) ∈ U from ⟨hs, by constructor <;> linarith⟩)).2
  let P := P0.restrOpen (Do (2 * R)) hDo
  let A := A0.restrOpen U hU
  have hPsource : P.source = Do (2 * R) := inter_eq_right.mpr hDoP
  have hAsource : A.source = U := inter_eq_right.mpr (hUW.trans inter_subset_left)
  have hPs : ContDiffOn ℝ ∞ P P.source := hP0s.mono inter_subset_left
  have hPi : ContDiffOn ℝ ∞ P.symm P.target := hP0i.mono inter_subset_left
  have hAs : ContDiffOn ℝ ∞ A A.source := hA0s.mono inter_subset_left
  have hAi : ContDiffOn ℝ ∞ A.symm A.target := hA0i.mono inter_subset_left
  have hPform (s : ℝ × ℝ) (hs : s ∈ P.source) :
      D.morse.symm s ∈ D.protectedSet ∧ P s = pi (j (D.morse.symm s)) :=
    hP0form s hs.1
  have hAform (v : (ℝ × ℝ) × ℝ) (hv : v ∈ A.source) :
      A v = L.symm (P v.1, v.2) ∧ H (A v) = v.2 ∧
        (A v ∈ S ↔ v.2 = c + Q v.1) := by
    have hfst : v.1 ∈ P0.source := (hUW hv.2).2
    rcases hA0form v hv.1 with ⟨_, hfwd, hheight, hgraph⟩
    refine ⟨?_, hheight, ?_⟩
    · change A0 v = L.symm (P0 v.1, v.2)
      rw [(hP0form v.1 hfst).2]
      exact hfwd
    · change A0 v ∈ range (fun q : UnitTwoSphere => psi (q, 0)) ↔
        v.2 = ⟪(u : E3), psi (D.point, 0)⟫_ℝ +
          (D.morseSign1 * v.1.1 ^ 2 + D.morseSign2 * v.1.2 ^ 2)
      simpa only [add_assoc] using hgraph
  have h0Do : (0 : ℝ × ℝ) ∈ Do (2 * R) := by
    change (0 : ℝ) ^ 2 + 0 ^ 2 < (2 * R) ^ 2
    nlinarith [sq_pos_of_pos hR]
  have h0new : ((0 : ℝ × ℝ), c) ∈ A.source := by
    rw [hAsource]
    exact ⟨h0Do, by constructor <;> linarith⟩
  have hPcenter : P 0 = pi (j D.point) := hP00
  have hAcenter : A (0, c) = j D.point := by
    rw [(hAform (0, c) h0new).1, hPcenter]
    exact heightPlaneCoordinates_reconstruct u (j D.point) c rfl
  have htarget : A.target = L.symm ''
      (P.target ×ˢ Ioo (c - 8 * b) (c + 8 * b)) := by
    ext y
    constructor
    · intro hy
      have hs := A.map_target hy
      have hsU : A.symm y ∈ U := hAsource ▸ hs
      refine ⟨(P (A.symm y).1, (A.symm y).2),
        ⟨P.map_source (hPsource.symm ▸ hsU.1), hsU.2⟩, ?_⟩
      exact ((hAform (A.symm y) hs).1).symm.trans (A.right_inv hy)
    · rintro ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩
      have hs : (P.symm x, z) ∈ A.source := by
        rw [hAsource]
        exact ⟨hPsource ▸ P.map_target hx, hz⟩
      have heq : A (P.symm x, z) = L.symm (x, z) := by
        rw [(hAform (P.symm x, z) hs).1, P.right_inv hx]
      exact heq ▸ A.map_source hs
  have hinverse (y : E3) (hy : y ∈ A.target) :
      A.symm y = (P.symm (pi y), H y) := by
    have hs := A.map_target hy
    have hsU : A.symm y ∈ U := hAsource ▸ hs
    have hforward := (hAform (A.symm y) hs).1
    rw [A.right_inv hy] at hforward
    have hcoords : L y = (P (A.symm y).1, (A.symm y).2) := by
      exact (congrArg L hforward).trans (L.apply_symm_apply _)
    apply Prod.ext
    · change (A.symm y).1 = P.symm (L y).1
      rw [hcoords, P.left_inv (hPsource.symm ▸ hsU.1)]
    · exact (hAform (A.symm y) hs).2.1.symm.trans (congrArg H (A.right_inv hy))
  have hB : B R ⊆ P.source := by
    intro s hs
    rw [hPsource]
    change s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2
    have hs' : s.1 ^ 2 + s.2 ^ 2 ≤ R ^ 2 := hs
    nlinarith [sq_pos_of_pos hR]
  have hBA : B R ×ˢ Icc (c - 4 * b) (c + 4 * b) ⊆ A.source := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    rw [hAsource]
    exact ⟨hPsource ▸ hB hs, by constructor <;> linarith [hz.1, hz.2]⟩
  have hcapgap (i : Fin D.capCount) (y : E3) (hy : y ∈ (D.cap i).cap) :
      8 * b < |H y - c| := by linarith [hgap i y hy]
  have hcore (q : UnitTwoSphere) (hq : |f q - c| ≤ 8 * b) : q ∈ D.sourceCore := by
    have hcover : q ∈ D.sourceCore ∪ ⋃ i, (D.cap i).sourceCap :=
      D.source_cover.symm ▸ mem_univ q
    rcases hcover with hqCore | hqCap
    · exact hqCore
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hqCap
      exact False.elim ((not_le_of_gt (hcapgap i (j q) ⟨q, hi, rfl⟩)) hq)
  refine ⟨R, b, P, A, hR, hb, hPsource, hAsource, hPs, hPi, hAs, hAi,
    (fun _ hs => hs.1.1), hPform, hPcenter, hAcenter, htarget, hAform,
    hinverse, hB, hBA, ?_, hcapgap, hcore, ?_⟩
  · intro s hs z hz
    have hsz : (s, z) ∈ A.source := hBA ⟨hs, by
      obtain ⟨hlo, hhi⟩ := abs_le.mp hz
      constructor <;> linarith⟩
    refine ⟨(hAform (s, z) hsz).1, ?_⟩
    rw [← (hAform (s, z) hsz).1]
    exact A.left_inv hsz
  · intro q hq hnot hzero
    have hqCore := hcore q (hq.trans (by linarith))
    have heq : q = D.point := (D.unique_critical q hqCore).mp hzero
    subst q
    apply hnot
    refine ⟨0, ?_, hPcenter⟩
    change (0 : ℝ) ^ 2 + 0 ^ 2 < (R / 4) ^ 2
    nlinarith [sq_pos_of_pos hR]

end PoincareConjecture.M25.Topology3D
