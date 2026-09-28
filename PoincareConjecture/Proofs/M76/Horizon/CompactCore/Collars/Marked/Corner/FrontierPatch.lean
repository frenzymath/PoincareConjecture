import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Marked.TransversePatch



set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem OriginalSurfacePairChart.exists_corner_frontier_patch
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R S T D : Set X} {y : X}
    {j : V2 → X} (hD : j '' Disk ⊆ D)
    (B : OriginalSurfacePairChart e D T y true)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source) (σ : ℝ)
    (hS : ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ S ↔ (B.coordinates z).1.2 = 0)
    (hfront : ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔
      ((B.coordinates z).1.2 = 0 ∧ 0 ≤ σ * (B.coordinates z).1.1) ∨
      ((B.coordinates z).1.1 = 0 ∧ 0 ≤ (B.coordinates z).1.2))
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {p : E → X} (hp : PolyhedralPLInCharts e p K.space) (hpi : InjOn p K.space)
    (hps : MapsTo p K.space B.chart.source)
    (hpc : MapsTo (B.chart ∘ p) K.space B.coordinates.source)
    (hpD : MapsTo p K.space (j '' Disk)) (hpfront : MapsTo p K.space (frontier R)) :
    ∃ F : E × ℝ → X, PolyhedralPLInCharts e F (K.space ×ˢ I) ∧
      InjOn F (K.space ×ˢ I) ∧ MapsTo F (K.space ×ˢ I) (frontier R) ∧
      (∀ x ∈ K.space, F (x, 0) = p x) ∧
      (∀ z ∈ K.space ×ˢ I, F z ∈ j '' Disk ↔ z.2 = 0) ∧
      ∀ z ∈ K.space ×ˢ I, (F z ∈ S ↔ p z.1 ∈ S) ∧ (F z ∈ T ↔ p z.1 ∈ T) := by
  obtain ⟨δ, F, _, _, hF, hFi, hFs, hFc, hcenter, hcoordinates, hFD, hFT⟩ :=
    B.exists_transverse_patch hcover K hK hp hpi hps hpc (fun x hx => hD (hpD hx))
  have hfirst (z) (hz : z ∈ K.space ×ˢ I) :
      (B.coordinates (B.chart (F z))).1 = (B.coordinates (B.chart (p z.1))).1 := by
    simpa only using congrArg Prod.fst (hcoordinates z hz)
  have hSmark (z) (hz : z ∈ K.space ×ˢ I) : F z ∈ S ↔ p z.1 ∈ S := by
    have h0 := hS (B.chart (F z)) (hFc hz)
    have h1 := hS (B.chart (p z.1)) (hpc hz.1)
    rw [B.chart.left_inv (hFs hz)] at h0
    rw [B.chart.left_inv (hps hz.1)] at h1
    rw [hfirst z hz] at h0
    exact h0.trans h1.symm
  refine ⟨F, hF, hFi, ?_, hcenter, ?_, fun z hz => ⟨hSmark z hz, hFT z hz⟩⟩
  · intro z hz
    have h0 := hfront (B.chart (F z)) (hFc hz)
    have h1 := hfront (B.chart (p z.1)) (hpc hz.1)
    rw [B.chart.left_inv (hFs hz)] at h0
    rw [B.chart.left_inv (hps hz.1)] at h1
    rw [hfirst z hz] at h0
    exact h0.mpr (h1.mp (hpfront hz.1))
  · intro z hz
    constructor
    · intro h
      exact (hFD z hz).mp (hD h)
    · intro h
      have heq : z = (z.1, 0) := Prod.ext rfl h
      rw [heq, hcenter z.1 hz.1]
      exact hpD hz.1

end PoincareConjecture.M76
