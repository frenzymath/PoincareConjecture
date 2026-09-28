import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckOverlapCapture
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckRicciComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.ProjectionDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Diffeomorph.Sphere











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

private abbrev CI := (𝓡 2).prod 𝓘(ℝ, ℝ)





theorem exists_buffered_neck_sphere_graph_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M]
        (g : RiemannianMetric 3 M) (_D : LeviCivitaData g)
        (N N' : EpsilonNeck g),
        N.epsilon ≤ epsilon₀ → N'.epsilon ≤ epsilon₀ →
        ∀ a ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹, ∀ q : UnitTwoSphere,
          N'.coordinate_map (q, a) ∈ N.carrier →
          |(N.coordinate_inverse (N'.coordinate_map (q, a))).2| ≤
            3 * N.epsilon⁻¹ / 4 →
          ∃ phi : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
            (∀ p, phi p = (N.coordinate_inverse (N'.coordinate_map (p, a))).1) ∧
            ∃ f : UnitTwoSphere → ℝ,
              ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f ∧
              (∀ p, |f p| < 7 * N.epsilon⁻¹ / 8) ∧
              (∀ p, N'.coordinate_map (phi.symm p, a) = N.coordinate_map (p, f p)) ∧
              range (fun p : UnitTwoSphere => N'.coordinate_map (p, a)) =
                range (fun p : UnitTwoSphere => N.coordinate_map (p, f p)) := by
  obtain ⟨epsilonC, hCpos, hCsmall, hcapture⟩ :=
    exists_buffered_neck_sphere_capture_accuracy.{u}
  obtain ⟨epsilonR, hRpos, _, hricci⟩ := tube.exists_neck_ricci_accuracy.{u}
  obtain ⟨epsilonS, hSpos, _, hscales⟩ := exists_neck_overlap_scale_accuracy.{u}
  refine ⟨min epsilonC (min epsilonR epsilonS),
    lt_min hCpos (lt_min hRpos hSpos), (min_le_left _ _).trans hCsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g D N N' hN hN' a ha q hy haxis
  have hcap := hcapture M g D N N'
    (hN.trans (min_le_left _ _)) (hN'.trans (min_le_left _ _)) a ha q hy haxis
  have hcarrier (p : UnitTwoSphere) : N'.coordinate_map (p, a) ∈ N.carrier :=
    (hcap ⟨p, rfl⟩).1
  have hscale := hscales M g D N N'
    ((hN.trans (min_le_right _ _)).trans (min_le_right _ _))
    ((hN'.trans (min_le_right _ _)).trans (min_le_right _ _))
    ⟨N'.coordinate_map (q, a), hy, N'.coordinate_map_mem ⟨mem_univ _, ha⟩⟩
  have hRN := hricci M g D N
    ((hN.trans (min_le_right _ _)).trans (min_le_left _ _))
  have hRN' := hricci M g D N'
    ((hN'.trans (min_le_right _ _)).trans (min_le_left _ _))
  let F : UnitTwoSphere → UnitTwoSphere :=
    fun p => (N.coordinate_inverse (N'.coordinate_map (p, a))).1
  have hinverse : ContMDiff (𝓡 2) CI ∞
      (fun p : UnitTwoSphere => N.coordinate_inverse (N'.coordinate_map (p, a))) :=
    N.coordinate_inverse_smooth.comp_contMDiff (N'.sphereSlice_contMDiff ha) hcarrier
  have hF : ContMDiff (𝓡 2) (𝓡 2) ∞ F :=
    contMDiff_fst.comp hinverse
  have hbij (p : UnitTwoSphere) :
      Function.Bijective (mfderiv (𝓡 2) (𝓡 2) F p) :=
    N.sphereSlice_projection_mfderiv_bijective_of_ricci_error D N' ha p
      (hcarrier p) hscale.2.le hRN hRN'
  have hsphere : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) _ (by norm_num)
  let : ConnectedSpace UnitTwoSphere := Subtype.connectedSpace hsphere
  let phi : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞ :=
    Poincare.Geometry.Manifold.sphereDiffeomorphOfLocalDiffeomorph (n := 0) F
      (Poincare.isLocalDiffeomorph_of_contMDiff_bijective_mfderiv hF hbij)
  have hphi (p : UnitTwoSphere) : phi p = F p := rfl
  let f : UnitTwoSphere → ℝ :=
    fun p => (N.coordinate_inverse (N'.coordinate_map (phi.symm p, a))).2
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f :=
    contMDiff_snd.comp (hinverse.comp phi.symm.contMDiff)
  have hbuffer (p : UnitTwoSphere) : |f p| < 7 * N.epsilon⁻¹ / 8 := by
    exact abs_lt.mpr (hcap ⟨phi.symm p, rfl⟩).2
  have hpoint (p : UnitTwoSphere) :
      N'.coordinate_map (phi.symm p, a) = N.coordinate_map (p, f p) := by
    have hcoords : N.coordinate_inverse (N'.coordinate_map (phi.symm p, a)) =
        (p, f p) := by
      apply Prod.ext
      · change F (phi.symm p) = p
        rw [← hphi]
        exact phi.apply_symm_apply p
      · rfl
    calc
      N'.coordinate_map (phi.symm p, a) =
          N.coordinate_map (N.coordinate_inverse (N'.coordinate_map (phi.symm p, a))) :=
        (N.coordinate_map_coordinate_inverse (hcarrier (phi.symm p))).symm
      _ = N.coordinate_map (p, f p) := congrArg N.coordinate_map hcoords
  refine ⟨phi, hphi, f, hf, hbuffer, hpoint, ?_⟩
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨phi p, ?_⟩
    simpa only [phi.symm_apply_apply] using (hpoint (phi p)).symm
  · rintro ⟨p, rfl⟩
    exact ⟨phi.symm p, hpoint p⟩

end PoincareConjecture.M28
