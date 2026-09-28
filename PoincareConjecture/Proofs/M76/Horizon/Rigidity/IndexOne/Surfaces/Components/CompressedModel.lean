import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.Components.CommonComponent
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.Incidence.TwoRimModel

set_option autoImplicit false
open Set Metric Geometry BrownCollar

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))
local notation "Q2" => sphere (0 : V2) 1

open Classical in

theorem exists_compressed_sourceSurface_common_component_model
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d) (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    {u v : ℝ} {theta theta' : C}
    (heN : PLDomain e (sourceSlab phi u v))
    (hfront : frontier (sourceSlab phi u v) = (sourceSlab phi u v ∩ frontier R) ∪
      (sourceSurface phi theta ∪ sourceSurface phi theta'))
    (hAB : Disjoint (sourceSurface phi theta) (sourceSurface phi theta'))
    (hcorner : ∀ x ∈ sourceSurface phi theta ∩ frontier R,
      ∃ (psi lambda : V3 →ᴬ[ℝ] ℝ) (w z : V3) (G : OpenPartialHomeomorph X V3),
        psi.contLinear w = 1 ∧ psi.contLinear z = 0 ∧ lambda.contLinear z = 1 ∧
        x ∈ G.source ∧ psi (G x) = 0 ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi u v ↔ 0 ≤ psi (G y)) ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi u v ∩ frontier R ↔
          psi (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
        ∀ y ∈ G.source, y ∈ sourceSurface phi theta ↔
          psi (G y) = 0 ∧ lambda (G y) ≤ 0)
    (hinj : ∀ x : sourceSurface phi theta, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSurface phi theta, X)) x)) :
    ∃ (s : Finset R) (F : X → (s → ℝ × V3)) (S : Set X)
      (K : SimplicialComplex ℝ (s → ℝ × V3))
      (J : Bool → SimplicialComplex ℝ (s → ℝ × V3))
      (G : K.space ≃ₜ S) (g : (s → ℝ × V3) → X)
      (gamma : ∀ side, Q2 ≃ₜ (J side).space)
      (delta : ∀ side, C ≃ₜ (J side).space)
      (hJK : ∀ side, J side ≤ K),
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      InjOn F R ∧ S ⊆ sourceSurface phi theta ∧
      (∀ x ∈ S, connectedComponentIn (sourceSurface phi theta) x = S) ∧
      K.faces.Finite ∧ K.space = F '' S ∧
      (∀ x : S, (G.symm x : s → ℝ × V3) = F x) ∧
      (∀ z : K.space, (G z : X) = g z) ∧
      PolyhedralPLInCharts e g K.space ∧
      (∀ t ∈ K.faces, ∃ q ∈ K.faces, q.card = 3 ∧ t ⊆ q) ∧
      (∀ w ∈ K.vertices, IsConnected (K.link w).space) ∧ IsPathConnected K.space ∧
      (∀ t ∈ K.faces, t.card = 2 →
        {q : Finset (s → ℝ × V3) | q ∈ K.faces ∧ q.card = 3 ∧ t ⊆ q}.ncard =
          if ∃ side, t ∈ (J side).faces then 1 else 2) ∧
      Pairwise (fun a b => Disjoint (J a).space (J b).space) ∧
      (∀ side, (gamma side).IsFinitePL) ∧
      (∀ side c, (delta side c : s → ℝ × V3) = F (sourceBoundaryCircle phi theta F0
        (originalIntervalEndpoint side) (originalIntervalEndpoint_norm side) c : X)) ∧
      (∀ side c, (sourceBoundaryCircle phi theta F0 (originalIntervalEndpoint side)
        (originalIntervalEndpoint_norm side) c : X) ∈ S) ∧
      ∀ side, Function.Bijective (FundamentalGroup.map
        (ContinuousMap.inclusion (SimplicialComplex.space_subset_of_le (hJK side))) (delta side 0)) ∧
        ∀ x : (J side).space,
          ∃ c : OpenPartialHomeomorph ((J side).space × Ico (0 : ℝ) 1) K.space,
            collarBase x ∈ c.source ∧ ∀ a, collarBase a ∈ c.source →
              c (collarBase a) = Set.inclusion (SimplicialComplex.space_subset_of_le (hJK side)) a := by
  classical
  obtain ⟨s, F, K0, A, J, Hmodel, g, j, gamma, hFc, hF, hFi, hK0, _, _,
    _, _, hHF, hHg, hgPL, _, _, hpure, hcofaces, hlinks, _, hJA, hdis, _, _, _,
    hgamma, hval⟩ :=
    exists_compressed_sourceSurface_two_rim_incidence_model
      e d hd phi hphi F0 heN hfront hAB hcorner
  let : DecidableEq (s → ℝ × V3) := Classical.decEq _
  let delta (side : Bool) : C ≃ₜ (J side).space :=
    (sourceRimCircleCoordinates phi theta F0 (originalIntervalEndpoint side)
      (originalIntervalEndpoint_norm side)).trans ((j side).symm.trans (gamma side))
  have hdelta (side : Bool) (c : C) : (delta side c : s → ℝ × V3) =
      F (sourceBoundaryCircle phi theta F0 (originalIntervalEndpoint side)
        (originalIntervalEndpoint_norm side) c : X) := by
    change (gamma side ((j side).symm
      (sourceRimCircleCoordinates phi theta F0 (originalIntervalEndpoint side)
        (originalIntervalEndpoint_norm side) c)) : s → ℝ × V3) = _
    rw [hval, (j side).apply_symm_apply]
    rfl
  obtain ⟨U, hU, collar, hbase⟩ := exists_sourcePhase_rim_collar e phi F0 heN hfront hAB (by
    intro x hx
    obtain ⟨psi, lambda, w, z, T, hw, hz, hlz, hxT, _, _, hslab, hold, hphase⟩ := hcorner x hx
    exact ⟨psi, lambda, w, z, T, hw, hz, hlz, hxT, hslab, hold, hphase⟩)
  obtain ⟨D, hJD, hP, hpP, hlP, hcP, heP, hrim⟩ :=
    exists_common_rim_component_of_source_model phi theta F0 K0 hK0 Hmodel F hFc hHF
      (fun t ht => by
        obtain ⟨q, hq, htq, hqc⟩ := hpure t ht
        exact ⟨q, hq, hqc, htq⟩)
      (by intro w hw; convert! hlinks w hw) J (fun side => (hJA side).2.1)
      gamma (fun side => (hgamma side).1)
      hcofaces delta hdelta hinj hU collar hbase
  obtain ⟨S, G, hSF, hcomponent, hG, hGF⟩ :=
    exists_source_component_of_model K0 hK0 Hmodel F hFc hHF D
  have hPS : (K0.edgeComponentComplex D).space = F '' S := by
    ext z
    constructor
    · intro hz
      exact ⟨G ⟨z, hz⟩, (G ⟨z, hz⟩).property, by rw [← hGF, G.symm_apply_apply]⟩
    · rintro ⟨x, hx, rfl⟩
      rw [← hGF ⟨x, hx⟩]
      exact (G.symm ⟨x, hx⟩).property
  have hpoint (side : Bool) (c : C) :
      (G (Set.inclusion (SimplicialComplex.space_subset_of_le (hJD side)) (delta side c)) : X) =
        (sourceBoundaryCircle phi theta F0 (originalIntervalEndpoint side)
          (originalIntervalEndpoint_norm side) c : X) := by
    rw [hG]
    apply congrArg Subtype.val
    apply Hmodel.symm.injective
    apply Subtype.ext
    rw [Hmodel.symm_apply_apply, hHF]
    exact hdelta side c
  refine ⟨s, F, S, K0.edgeComponentComplex D, J, G, g, gamma, delta, hJD,
    hFc, hF, hFi, hSF, hcomponent, hP, hPS, hGF, ?_, ?_, hpP, ?_, hcP,
    heP, hdis, fun side => (hgamma side).1, hdelta, ?_, hrim⟩
  · intro z
    rw [hG, hHg]
  · exact hgPL.restrict_finite _ hP
      (SimplicialComplex.space_subset_of_le (K0.edgeComponentComplex_le D))
  · intro w hw
    convert! hlP w hw
  · intro side c
    rw [← hpoint side c]
    exact (G _).property

end PoincareConjecture.M76.HamiltonIntervalTorus
