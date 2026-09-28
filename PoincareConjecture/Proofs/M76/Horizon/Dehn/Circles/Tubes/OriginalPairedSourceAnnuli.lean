import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.PairedSourceAnnuli
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.PairedTubeMap

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn
local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => (P2 × ℝ)
local notation "D2" => Metric.closedBall (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
  {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}

theorem OrdinaryIntervalMarkedModel.exists_original_paired_source_annuli
    (D : OrdinaryIntervalMarkedModel old i) (hcore : D.core ⊆ interior R)
    {m : ℕ} (P : Polygon V2 (m + 3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P) (hPs : P.boundary ℝ = old.pieces i)
    {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) :
    letI : Fintype D.complex.faces := D.complex_finite.fintype
    ∃ (N : ℕ) (sigma : C3 → D.sample → ℝ × V3) (tau : C3 → X)
      (A : Fin 2 → Set V2) (c : ∀ j, squareAnnulus L d ≃ₜ A j),
      FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (N + 3)) ∧
      sigma '' (signedTubeDiamond ×ˢ Icc (0 : ℝ) (N + 3)) =
        (D.complex.barycentricNeighborhood (D.marks (.inr 2))).space ∧
      MapsTo sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (N + 3)) D.complex.space ∧
      (∀ k (x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (N + 3))),
        sigma x ∈ (D.marks (.inr k.castSucc)).space ↔ (x : C3).1 ∈ signedTubeSheet k) ∧
      (∀ x : ↥(signedTubeDiamond ×ˢ Icc (0 : ℝ) (N + 3)),
        sigma x ∈ (D.marks (.inr 2)).space ↔ (x : C3).1 = (0, 0)) ∧
      (∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (N + 3),
        ∀ y ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (N + 3),
        sigma x = sigma y ↔ x.1 = y.1 ∧
          (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = N + 3) ∨ (x.2 = N + 3 ∧ y.2 = 0))) ∧
      tau = (fun z => (D.inverse (sigma (periodicTubeCoordinates L d 0 (N + 3) z)) : X)) ∧
      PolyhedralPLInCharts e tau (_root_.Dehn.identityTube L d) ∧
      MapsTo tau (_root_.Dehn.identityTube L d) (interior R) ∧
      (∀ z ∈ _root_.Dehn.identityTube L d, ∀ w ∈ _root_.Dehn.identityTube L d,
        tau z = tau w ↔ z.1 = w.1 ∧
          (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L))) ∧
      tau '' _root_.Dehn.identityTube L d =
        (fun z => (D.inverse z : X)) ''
          (D.complex.barycentricNeighborhood (D.marks (.inr 2))).space ∧
      (∀ j : Fin 2, ∀ z ∈ _root_.Dehn.identityTube L d,
        tau z ∈ f '' (D.source j.castSucc).space ↔
          z.1.2 = if j = 0 then z.1.1 else -z.1.1) ∧
      (∀ j : Fin 2, ∀ z ∈ _root_.Dehn.identityTube L d,
        tau z ∈ f '' (D.clips j.castSucc).space ↔
          z.1.2 = if j = 0 then z.1.1 else -z.1.1) ∧
      (∀ j, (c j).IsFinitePL ∧ (c j).symm.IsFinitePL) ∧
      (∀ j, A j ⊆ (D.clips j.castSucc).space) ∧ Disjoint (A 0) (A 1) ∧
      (∀ (j : Fin 2) (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
        f (c j ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
          _root_.Dehn.annulus_period_point_mem hd hwidth _ u⟩) =
        tau (sourceTubeDiagonal j u, s)) ∧
      (∀ (j : Fin 2) (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
        D.graph (f (c j ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
          _root_.Dehn.annulus_period_point_mem hd hwidth _ u⟩)) =
        sigma (periodicTubeCoordinates L d 0 (N + 3) (sourceTubeDiagonal j u, s))) ∧
      (∀ j (p : squareAnnulus L d),
        (c j p : V2) ∈ old.pieces (if j = 0 then i else old.mate i) ↔ depth L p = 0) ∧
      (∀ j, (fun p : squareAnnulus L d => (c j p : V2)) '' {p | depth L p = 0} =
        old.pieces (if j = 0 then i else old.mate i)) ∧
      D2 ∩ f ⁻¹' (tau '' _root_.Dehn.identityTube L d) = A 0 ∪ A 1 := by
  classical
  let _ : Fintype D.complex.faces := D.complex_finite.fintype
  obtain ⟨N, closing, sigma, hPL, himage, hK, hsheet, haxis, haxisImage, hfib⟩ :=
    D.exists_signed_circle_tube hcore P hP hPi hPs
  obtain ⟨n, Q, hQ, hQi, hQs⟩ := old.exists_paired_circle_polygons P hP hPi hPs
  obtain ⟨A, c, hclosing, hc, hA, hdis, hvalue, hgraph, hmiddle, hmiddleImage, hpre⟩ :=
    D.exists_paired_source_annuli (by positivity : (0 : ℝ) < N + 3) hd hwidth
      sigma closing hPL hK hfib n Q hQ hQi hQs hsheet haxis haxisImage
  have hfib' : ∀ x ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (N + 3),
      ∀ y ∈ signedTubeDiamond ×ˢ Icc (0 : ℝ) (N + 3),
      sigma x = sigma y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = N + 3) ∨ (x.2 = N + 3 ∧ y.2 = 0)) := by
    intro x hx y hy
    rw [hfib ⟨x, hx⟩ ⟨y, hy⟩]
    simp only [Subtype.ext_iff, Prod.ext_iff, signedTubeReflection_apply,
      hclosing, ↓reduceIte, one_mul, Prod.eta]
    simp [and_or_left, and_assoc, and_comm, and_left_comm, eq_comm]
  have hL : 0 < L := by linarith
  have hN : (0 : ℝ) < N + 3 := by positivity
  let sigma' := sigma ∘ periodicTubeCoordinates L d 0 (N + 3)
  let tau : C3 → X := (fun z => (D.inverse z : X)) ∘ sigma'
  have hsigma' : FinitePiecewiseAffineOn sigma' (_root_.Dehn.identityTube L d) :=
    hPL.comp (periodicTubeCoordinates_finitePL hL hd 0 (N + 3))
      (periodicTubeCoordinates_mapsTo hL hd hN)
  have hsigmaK : MapsTo sigma' (_root_.Dehn.identityTube L d) D.complex.space :=
    fun z hz => hK (periodicTubeCoordinates_mapsTo hL hd hN hz)
  have htauPL : PolyhedralPLInCharts e tau (_root_.Dehn.identityTube L d) := by
    obtain ⟨J, hJ, hJs, hJa⟩ := hsigma'
    have hh := D.inverse_PL.comp_finitePiecewiseAffineOn J hJ
      (show FinitePiecewiseAffineOn sigma' J.space from ⟨J, hJ, rfl, hJa⟩)
      (by simpa only [hJs] using hsigmaK)
    simpa only [hJs] using hh
  have htauFib : ∀ z ∈ _root_.Dehn.identityTube L d, ∀ w ∈ _root_.Dehn.identityTube L d,
      tau z = tau w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)) := by
    intro z hz w hw
    have heq : tau z = tau w ↔ sigma' z = sigma' w := by
      constructor
      · intro h
        exact (D.graph_inverse _ (hsigmaK hz)).symm.trans
          ((congrArg D.graph h).trans (D.graph_inverse _ (hsigmaK hw)))
      · exact congrArg (fun q => (D.inverse q : X))
    exact heq.trans (normalized_identity_tube_fibers hL hd hN sigma hfib' z hz w hw)
  have htauImage : tau '' _root_.Dehn.identityTube L d =
      (fun z => (D.inverse z : X)) ''
        (D.complex.barycentricNeighborhood (D.marks (.inr 2))).space := by
    change ((fun z => (D.inverse z : X)) ∘
      (sigma ∘ periodicTubeCoordinates L d 0 (N + 3))) '' _ = _
    rw [image_comp, image_comp, periodicTubeCoordinates_image hL hd hN, himage]
  have htauSheet (j : Fin 2) (z : C3) (hz : z ∈ _root_.Dehn.identityTube L d) :
      tau z ∈ f '' (D.source j.castSucc).space ↔
        z.1.2 = if j = 0 then z.1.1 else -z.1.1 := by
    exact (D.mem_mark_image (D.marks_image j.castSucc) (sigma' z) (hsigmaK hz)).symm.trans
      ((hsheet j ⟨_, periodicTubeCoordinates_mapsTo hL hd hN hz⟩).trans
        (periodicTubeCoordinates_sheet hL hd hN j z hz))
  have htauClip (j : Fin 2) (z : C3) (hz : z ∈ _root_.Dehn.identityTube L d) :
      tau z ∈ f '' (D.clips j.castSucc).space ↔
        z.1.2 = if j = 0 then z.1.1 else -z.1.1 := by
    apply Iff.trans _ (htauSheet j z hz)
    constructor
    · rintro ⟨x, hx, hval⟩
      exact ⟨x, ((D.clips_data j.castSucc).2.1.subset hx).1, hval⟩
    · rintro ⟨x, hx, hval⟩
      refine ⟨x, (D.clips_data j.castSucc).2.1.symm.subset ⟨hx, ?_⟩, hval⟩
      change f x ∈ D.core
      exact hval.symm ▸ (D.inverse (sigma' z)).property
  refine ⟨N, sigma, tau, A, c, hPL, himage, hK, hsheet, haxis, hfib', rfl, htauPL,
    (fun z _ => hcore (D.inverse (sigma' z)).property), htauFib, htauImage,
    htauSheet, htauClip, hc, hA, hdis, hvalue, hgraph, ?_, ?_, hpre⟩
  · intro j p
    exact (hQs j) ▸ hmiddle j p
  · intro j
    exact (hmiddleImage j).trans (hQs j)

end PoincareConjecture.M76.Dehn
