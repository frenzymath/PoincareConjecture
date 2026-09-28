import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.FreeEnergyLimit
import Mathlib.Topology.Order.IsLUB

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin m)

theorem observedWeakAnnulus_free_infimum_limit
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsClosedEmbedding e)
    (hread : M60.SUChartReadable (n := n) e) (c0 c1 : ℝ → M)
    (hc0 : Continuous c0) (hc1 : Continuous c1)
    (hp0 : Function.Periodic c0 curvePeriod) (hp1 : Function.Periodic c1 curvePeriod)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ q, ‖B q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ B q v v) (hsymm : ∀ q v w, B q v w = B q w v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * B q v v)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (A0 : M64ObservedWeakAnnulus (n := n) e c0 c1) :
    ∃ (r0 : ℝ) (L0 L1 : ℝ → ℝ)
      (L : M64ObservedWeakAnnulus (n := n) e (c0 ∘ L0) (c1 ∘ L1)),
      r0 ∈ Icc lo hi ∧ Monotone L0 ∧ Monotone L1 ∧
      (∀ x, L0 (x + curvePeriod) = L0 x + curvePeriod) ∧
      (∀ x, L1 (x + curvePeriod) = L1 x + curvePeriod) ∧
      L0 0 ∈ Icc (0 : ℝ) curvePeriod ∧ L1 0 ∈ Icc (0 : ℝ) curvePeriod ∧
      ∀ s ∈ Icc lo hi, ∀ sigma0 sigma1 : M64PeriodicDegreeOneLift,
        ∀ A : M64ObservedWeakAnnulus (n := n) e
          (c0 ∘ sigma0.map) (c1 ∘ sigma1.map),
        L.weightedEnergy B r0 ≤ A.weightedEnergy B s := by
  classical
  let X := (sigma0 : M64PeriodicDegreeOneLift) ×
    (sigma1 : M64PeriodicDegreeOneLift) ×
      Icc lo hi × M64ObservedWeakAnnulus (n := n) e
        (c0 ∘ sigma0.map) (c1 ∘ sigma1.map)
  let T : Set ℝ := range (fun P : X => P.2.2.2.weightedEnergy B P.2.2.1)
  have hne : T.Nonempty := by
    refine ⟨A0.weightedEnergy B lo, ?_⟩
    exact ⟨⟨M64PeriodicDegreeOneLift.identity, M64PeriodicDegreeOneLift.identity,
      ⟨lo, le_rfl, hlohi⟩, A0⟩, rfl⟩
  have hlower : BddBelow T := by
    refine ⟨0, ?_⟩
    rintro _ ⟨P, rfl⟩
    exact P.2.2.2.weightedEnergy_nonneg B hpos (hlo.le.trans P.2.2.1.property.1)
  obtain ⟨u, -, hlim, hu⟩ := exists_seq_tendsto_sInf hne hlower
  change ∀ j, ∃ P : X, P.2.2.2.weightedEnergy B P.2.2.1 = u j at hu
  choose P hP using hu
  let r : ℕ → ℝ := fun j => (P j).2.2.1
  let sigma0 := fun j => (P j).1
  let sigma1 := fun j => (P j).2.1
  let A := fun j => (P j).2.2.2
  have hr (j : ℕ) : r j ∈ Icc lo hi := (P j).2.2.1.property
  have hA (j : ℕ) : (A j).weightedEnergy B (r j) = u j := hP j
  have henergy : Tendsto (fun j => (A j).weightedEnergy B (r j)) atTop (𝓝 (sInf T)) := by
    simpa only [hA] using hlim
  obtain ⟨-, r0, L0, L1, L, -, hr0, hL0, hL1, hP0, hP1,
      h00, h10, -, -, -, -, hE⟩ :=
    observedWeakAnnulus_free_energy_limit e he hei hread c0 c1 hc0 hc1 hp0 hp1
      B hB hK hb hpos hsymm hC hcoercive hlo r hr sigma0 sigma1 A henergy
  refine ⟨r0, L0, L1, L, hr0, hL0, hL1, hP0, hP1, h00, h10, ?_⟩
  intro s hs tau0 tau1 D
  exact hE.trans (csInf_le hlower ⟨⟨tau0, tau1, ⟨s, hs⟩, D⟩, rfl⟩)

end PoincareConjecture.M64
