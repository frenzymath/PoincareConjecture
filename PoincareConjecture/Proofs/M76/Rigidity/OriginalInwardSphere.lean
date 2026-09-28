import PoincareConjecture.Proofs.M76.Rigidity.OriginalChartBall
import PoincareConjecture.Proofs.M76.Rigidity.InwardCollarLevelSphere
import PoincareConjecture.Proofs.M76.PrimeReduction.ProtectedBoundaryCollar










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

open Classical in




theorem exists_original_inward_sphere
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X}
    (hR : IsCompact R) (he : PLDomain e R) (hne : (interior R).Nonempty)
    (sph : ChartwisePLSphere e (frontier R))
    (hU : IsOpen U) (hBU : frontier R ⊆ U) :
    ∃ (s : Finset R) (L : SimplicialComplex ℝ (s → ℝ × V3))
      (HB : L.space ≃ₜ frontier R) (c : (s → ℝ × V3) × ℝ → X),
      L.faces.Finite ∧ PolyhedralPLInCharts e c (L.space ×ˢ I) ∧
      Topology.IsEmbedding (fun z : (L.space ×ˢ I : Set ((s → ℝ × V3) × ℝ)) => c z) ∧
      MapsTo c (L.space ×ˢ I) R ∧
      (∀ x : L.space, c ((x : s → ℝ × V3), 0) = HB x) ∧
      (∀ z : (L.space ×ˢ I : Set ((s → ℝ × V3) × ℝ)),
        c z ∈ frontier R ↔ (z : (s → ℝ × V3) × ℝ).2 = 0) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ MapsTo c (L.space ×ˢ Icc 0 δ) U ∧
        (∀ ε : ℝ, 0 < ε → ε ≤ δ →
          IsOpen ((Subtype.val : R → X) ⁻¹' (c '' (L.space ×ˢ Ico 0 ε)))) ∧
        Nonempty (ChartwisePLSphere e (c '' (L.space ×ˢ {δ / 2}))) ∧
        c '' (L.space ×ˢ {δ / 2}) ⊆ interior R ∧
        c '' (L.space ×ˢ {δ / 2}) ⊆ U := by
  classical
  obtain ⟨D, _, hDR, ⟨b⟩⟩ := he.exists_ball_in_interior hne
  obtain ⟨s, L, HB, c, hL, hc, hi, hinside, hbase, hproper,
    δ, hδ, hδsmall, hthin, hopen⟩ := exists_protected_small_boundary_collar
      hR he (hDR.trans interior_subset) b hU hBU
  obtain ⟨hlevel, hlevelInt⟩ := sph.nonempty_collar_level he.compatible
    L hL HB c hc hi hbase hinside hproper (half_pos hδ) (by linarith)
  refine ⟨s, L, HB, c, hL, hc, hi, hinside, hbase, hproper,
    δ, hδ, hδsmall, hthin, hopen, hlevel, hlevelInt, ?_⟩
  rintro x ⟨z, hz, rfl⟩
  apply hthin
  refine ⟨hz.1, ?_⟩
  have hzt : z.2 = δ / 2 := mem_singleton_iff.mp hz.2
  rw [hzt]
  exact ⟨(half_pos hδ).le, by linarith⟩

end PoincareConjecture.M76
