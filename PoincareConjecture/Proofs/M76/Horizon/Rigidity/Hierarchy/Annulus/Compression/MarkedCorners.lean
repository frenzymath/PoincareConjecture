import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.SecondCoordinateSurface
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.MarkedRimCharts
import PoincareConjecture.Proofs.M76.Wall.ProtectedPLIntersection










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

theorem exists_hamiltonZero_second_slab_marked_corner_of_supported_map
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (phi eta : C(H0, H0)) {R A : Set X0} (hA : IsClosed A) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap eta x = hamiltonZeroAmbientMap phi x)
    {cut a b theta : ℝ} (ha : cut < a) (hab : a < b) (hb : b < cut + p)
    (htheta : theta ∈ ({a, b} : Set ℝ))
    (hreg : HamiltonZeroSecondCoordinateRegularity e R phi (theta : C0))
    {x : X0} (hx : x ∈ (R ∩ hamiltonZeroSecondCircleMap eta ⁻¹' {(theta : C0)}) ∩ frontier R) :
    let N := R ∩ hamiltonZeroSecondCircleMap eta ⁻¹' AddCircle.closedIntervalArc p a b
    let S := R ∩ hamiltonZeroSecondCircleMap eta ⁻¹' {(theta : C0)}
    ∃ (psi lambda : V3 →ᴬ[ℝ] ℝ) (w v : V3) (G : OpenPartialHomeomorph X0 V3),
      psi.contLinear w = 1 ∧ psi.contLinear v = 0 ∧ lambda.contLinear v = 1 ∧
      x ∈ G.source ∧ psi (G x) = 0 ∧
      (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ G.source, y ∈ N ↔ 0 ≤ psi (G y)) ∧
      (∀ y ∈ G.source, y ∈ N ∩ frontier R ↔ psi (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
      ∀ y ∈ G.source, y ∈ S ↔ psi (G y) = 0 ∧ lambda (G y) ≤ 0 := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  have hxA : x ∉ A := fun h => hx.2.2 (hAR h)
  have hqfixed (y : X0) (hy : y ∉ A) :
      hamiltonZeroSecondCircleMap eta y = hamiltonZeroSecondCircleMap phi y := by
    rw [hamiltonZeroSecondCircleMap_ambient, hamiltonZeroSecondCircleMap_ambient, hfixed y hy]
  have hxq : hamiltonZeroSecondCircleMap phi x = (theta : C0) :=
    (hqfixed x hxA).symm.trans hx.1.2
  obtain ⟨d, psi, ell, u, v, T, hd, hpu, hlv, hpv, hxT, hlx, hpx, hT, hR, hB, hq, _⟩ :=
    hreg.2 ⟨x, hx.1.1⟩ hx.2 hxq
  let T' := T.restrOpen Aᶜ hA.isOpen_compl
  have hT' (i : ι) : (e i).symm.trans T' ∈ piecewiseAffineGroupoid V3 :=
    (e i).piecewiseAffine_compatible_restrOpen_right T (hT i) hA.isOpen_compl
  have hq' (y : R) (hy : (y : X0) ∈ T'.source) :
      hamiltonZeroSecondCircleMap eta y = ((ell (T' y) + d : ℝ) : C0) := by
    rw [hqfixed y hy.2]
    exact hq y hy.1
  obtain ⟨lambda, v', G, hpv', hlv', hxG, _, hpG, hG, _, hGN, hGO, hGS⟩ :=
    HamiltonIntervalTorus.exists_relative_shifted_circle_endpoint_chart_with_tangent
      e p (fun y : R => hamiltonZeroSecondCircleMap eta y) ha hab hb htheta hd
      psi ell u v T' hpu hlv hpv ⟨hxT, hxA⟩ hpx hlx hT'
      (fun y hy => hR y hy.1) (fun y hy => hB y hy.1) hq'
  refine ⟨psi, lambda, u, v', G, hpu, hpv', hlv', hxG, hpG, hG, ?_, ?_, ?_⟩
  · intro y hy
    exact (show (y ∈ R ∧ hamiltonZeroSecondCircleMap eta y ∈ AddCircle.closedIntervalArc p a b) ↔
      (∃ _hy : y ∈ R, hamiltonZeroSecondCircleMap eta y ∈ AddCircle.closedIntervalArc p a b) from
        ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, hq⟩ => ⟨h, hq⟩⟩).trans (hGN y hy)
  · intro y hy
    apply Iff.trans _ (hGO y hy)
    exact ⟨fun h => ⟨h.2, h.1.1, h.1.2⟩, fun ⟨hB, hR, hq⟩ => ⟨⟨hR, hq⟩, hB⟩⟩
  · intro y hy
    exact (show (y ∈ R ∧ hamiltonZeroSecondCircleMap eta y = (theta : C0)) ↔
      (∃ _hy : y ∈ R, hamiltonZeroSecondCircleMap eta y = (theta : C0)) from
        ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, hq⟩ => ⟨h, hq⟩⟩).trans (hGS y hy)

end PoincareConjecture.M76
