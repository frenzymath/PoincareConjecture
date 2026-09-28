import PoincareConjecture.Proofs.M76.PrimeReduction.FiniteDomainTriangulation
import PoincareConjecture.Proofs.M76.PrimeReduction.CompatibleChartStars
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalDomainCharts
import PoincareConjecture.Proofs.M76.RelativeApproximation.ModelInverse










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]





theorem exists_protected_domain_chart_stars
    {e : ι → OpenPartialHomeomorph X V3} {R D : Set X}
    (hR : IsCompact R) (he : PLDomain e R) (hDR : D ⊆ R)
    (b : ChartwisePLBall e D (frontier D)) :
    ∃ (s : Finset R) (F : X → (s → ℝ × V3))
      (K : SimplicialComplex ℝ (s → ℝ × V3))
      (A : Fin 3 → SimplicialComplex ℝ (s → ℝ × V3))
      (H : R ≃ₜ K.space) (g : (s → ℝ × V3) → R),
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      K.faces.Finite ∧
      (∀ a, A a ≤ K ∧ (A a).faces.Finite ∧
        ∀ t ∈ K.faces, (∀ v ∈ t, v ∈ (A a).vertices) → t ∈ (A a).faces) ∧
      K.space = F '' R ∧ (A 0).space = F '' frontier R ∧
      (A 1).space = F '' D ∧ (A 2).space = F '' frontier D ∧
      (∀ x : R, (H x : s → ℝ × V3) = F x) ∧
      ContinuousOn g K.space ∧
      (∀ z : K.space, (g z : X) = (H.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z => (g z : X)) K.space ∧
      ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
        MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
        (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
        (B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
          ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) := by
  classical
  obtain ⟨s, F, K0, A0, H0, hFc, hF, hK0, hA0, hK0s, hB0s,
    hD0s, hS0s, hH0, _, hproj⟩ :=
    exists_protected_finite_domain_triangulation hR he hDR b
  let z0 : Metric.closedBall (0 : V3) 1 :=
    ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  let x0 : R := ⟨b.parametrization z0, hDR (b.parametrization z0).property⟩
  obtain ⟨g, hgc, hgval, hgPL⟩ :=
    exists_polyhedral_PL_model_inverse e K0 hK0 H0 F (subset_refl R) x0 hH0 hproj
  choose G hGpoint hGcompat hGkind using
    fun q : K0.space => he.exists_local_region_chart (g q)
  obtain ⟨K, A, hK, hKK0, hA, hstars⟩ :=
    hgPL.exists_full_compatible_chart_stars K0 hK0 G hGcompat hGpoint A0
      (fun a => (hA0 a).2.1)
      (fun a => SimplicialComplex.space_subset_of_le (hA0 a).1)
  let H : R ≃ₜ K.space := H0.trans (Homeomorph.setCongr hKK0.space_eq.symm)
  have hHF (x : R) : (H x : s → ℝ × V3) = F x := hH0 x
  have hgval' (z : K.space) : (g z : X) = (H.symm z : X) :=
    hgval ⟨z, hKK0.space_eq.subset z.property⟩
  have hgc' : ContinuousOn g K.space := hKK0.space_eq.symm ▸ hgc
  have hgPL' : PolyhedralPLInCharts e (fun z => (g z : X)) K.space :=
    hKK0.space_eq.symm ▸ hgPL
  refine ⟨s, F, K, A, H, g, hFc, hF, hK, ?_, hKK0.space_eq.trans hK0s,
    (hA 0).2.1.trans hB0s, (hA 1).2.1.trans hD0s, (hA 2).2.1.trans hS0s,
    hHF, hgc', hgval', hgPL', ?_⟩
  · exact fun a => ⟨(hA a).1, hK.subset (hA a).1, (hA a).2.2⟩
  · intro p hp
    obtain ⟨q, hmap, hface⟩ := hstars p hp
    refine ⟨G q, hmap, hGcompat q, hface, ?_⟩
    rcases hGkind q with hint | ⟨ell, v, hv, _, hhalf⟩
    · exact Or.inl hint
    · exact Or.inr ⟨ell, v, hv, hhalf⟩

end PoincareConjecture.M76
