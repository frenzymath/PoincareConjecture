import PoincareConjecture.Proofs.M76.Rigidity.MarkedMixedChartStars
import PoincareConjecture.Proofs.M76.Rigidity.DiskModelCoordinates
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.OriginalDiskStarNeighborhood

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem exists_intrinsic_proper_disk_chart_stars
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (hR : IsCompact R) (he : PLDomain e R) {j : V2 → X}
    (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hDR : MapsTo j D R)
    (hproper : ∀ z : D, j z ∈ frontier R ↔ (z : V2) ∈ Q)
    (G : D → OpenPartialHomeomorph X C3)
    (hGpoint : ∀ z : D, j z ∈ (G z).source)
    (hGcompat : ∀ z i, LocallyPiecewiseAffineOn
      ((e i).symm.trans (G z)) ((e i).symm.trans (G z)).source) :
    ∃ (s : Finset R) (F : X → (s → ℝ × V3)) (C : Set X)
      (K : SimplicialComplex ℝ (s → ℝ × V3))
      (A : Fin 4 → SimplicialComplex ℝ (s → ℝ × V3))
      (H : C ≃ₜ K.space) (g : (s → ℝ × V3) → C) (u : (s → ℝ × V3) → V2),
      IsCompact C ∧ R ⊆ interior C ∧ Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      K.faces.Finite ∧
      (∀ i, A i ≤ K ∧ (A i).faces.Finite ∧
        ∀ t ∈ K.faces, (∀ v ∈ t, v ∈ (A i).vertices) → t ∈ (A i).faces) ∧
      K.space = F '' C ∧ (A 0).space = F '' R ∧
      (A 1).space = F '' frontier R ∧ (A 2).space = F '' (j '' D) ∧
      (A 3).space = F '' (j '' Q) ∧
      (A 2).space ∩ (A 1).space = (A 3).space ∧
      (∀ x : C, (H x : s → ℝ × V3) = F x) ∧
      ContinuousOn g K.space ∧
      (∀ z : K.space, (g z : X) = (H.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z => (g z : X)) K.space ∧
      K.AffineOnFaces u ∧ (∀ z : D, u (F (j z)) = (z : V2)) ∧
      (∀ x ∈ C, ∃ (i : ι) (V : Set X) (a : (s → ℝ × V3) →ᴬ[ℝ] V3),
        IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ F) (e i) V) ∧
      ∀ p ∈ (A 2).vertices, ∃ z : D,
        MapsTo (fun w => (g w : X)) (K.closedStar p).space (G z).source ∧
        (K.closedStar p).AffineOnFaces (fun w => G z (g w)) ∧
        InjOn (fun w => G z (g w)) (K.closedStar p).space ∧
        (∃ O : Set X, IsOpen O ∧ (g p : X) ∈ O ∧ O ⊆ (G z).source ∧
          O ⊆ (fun w => (g w : X)) '' (K.closedStar p).space) ∧
        G z (g p) ∈ interior ((fun w => G z (g w)) '' (K.closedStar p).space) := by
  classical
  obtain ⟨s, F, C, K0, A0, H0, g, u, hC, hRCint, hFc, hF, hK0, hA0,
    hK0s, hA00, hA01, hA02, hA03, hA0int, hH0, hgc, hg, hgPL, huface, hu, hproj⟩ :=
    exists_intrinsic_proper_disk_neighborhood_model hR he hj hemb hDR hproper
  have hDC : MapsTo j D C := fun _ hz => interior_subset (hRCint (hDR hz))
  have hparameter (x : (A0 2).space) :
      u x ∈ D ∧ j (u x) = (g x : X) :=
    disk_parameter_eq_model_inverse H0 F g hH0 hg hDC u hu (hA02.subset x.property)
  let z : (A0 2).space → D := fun x => ⟨u x, (hparameter x).1⟩
  let B (x : (A0 2).space) := G (z x)
  have hBpoint (x : (A0 2).space) : (g x : X) ∈ (B x).source := by
    rw [← (hparameter x).2]
    exact hGpoint (z x)
  obtain ⟨K, A, hK, hKK0, hA, hstars⟩ :=
    hgPL.exists_full_marked_mixed_chart_stars K0 hK0
      ((A0 2).isCompact_space_of_finite (hA0 2).2.1)
      (SimplicialComplex.space_subset_of_le (hA0 2).1)
      B (fun x i => hGcompat (z x) i) hBpoint
      (fun _ => univ) (fun _ => isOpen_univ) (fun _ => mem_univ _)
      A0 (fun a => (hA0 a).2.1)
      (fun a => SimplicialComplex.space_subset_of_le (hA0 a).1)
  let H : C ≃ₜ K.space := H0.trans (Homeomorph.setCongr hKK0.space_eq.symm)
  have hHF (x : C) : (H x : s → ℝ × V3) = F x := hH0 x
  have hg' (x : K.space) : (g x : X) = (H.symm x : X) :=
    hg ⟨x, hKK0.space_eq.subset x.property⟩
  have hA2 : (A 2).space = F '' (j '' D) := (hA 2).2.1.trans hA02
  have hAint : (A 2).space ∩ (A 1).space = (A 3).space := by
    rw [(hA 2).2.1, (hA 1).2.1, (hA 3).2.1]
    exact hA0int
  refine ⟨s, F, C, K, A, H, g, u, hC, hRCint, hFc, hF, hK, ?_,
    hKK0.space_eq.trans hK0s, (hA 0).2.1.trans hA00, (hA 1).2.1.trans hA01,
    hA2, (hA 3).2.1.trans hA03, hAint, hHF,
    hKK0.space_eq.symm ▸ hgc, hg', hKK0.space_eq.symm ▸ hgPL,
    hKK0.affineOnFaces huface, hu, hproj, ?_⟩
  · exact fun a => ⟨(hA a).1, hK.subset (hA a).1, (hA a).2.2⟩
  · intro p hp
    have hpK : p ∈ K.vertices := (hA 2).1 hp
    have hpA0 : p ∈ (A0 2).space :=
      (hA 2).2.1.subset ((A 2).vertices_subset_space hp)
    obtain ⟨x, _, hsource, hface⟩ := hstars p hpK hpA0
    have hpR : (g p : X) ∈ R := by
      obtain ⟨hpD, hpval⟩ := hparameter ⟨p, hpA0⟩
      rw [← hpval]
      exact hDR hpD
    obtain ⟨hinj, hO, hint⟩ :=
      K.exists_original_open_neighborhood_inside_closedStar hK H g hg'
        hpK (hRCint hpR) (G (z x)) hsource
    exact ⟨z x, hsource, hface, hinj, hO, hint⟩

end PoincareConjecture.M76
