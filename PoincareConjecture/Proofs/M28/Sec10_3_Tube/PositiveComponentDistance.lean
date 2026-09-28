import PoincareConjecture.Proofs.M28.Mathlib.LastClosedVisit
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckSpherePaths
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceEdgeMinimizerOverlap

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace PoincareConjecture.M28

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem intrinsicEDist_to_positive_component_le (N : EpsilonNeck g)
    (V : TopologicalSpace.Opens M) (hSV : N.central_sphere ⊆ (V : Set M))
    {P : Set M} (hPV : P ⊆ (V : Set M))
    (hcomponent : ∀ q ∈ P, connectedComponentIn N.central_sphereᶜ q ⊆ P)
    {q : M} (hq : q ∈ P) {B : ℝ} (hB : 0 < B)
    (hdist : g.edist N.center q < ENNReal.ofReal B) :
    intrinsicEDist g (V : Set M) N.center q ≤
      ENNReal.ofReal ((4 * standardSpherePathCeiling) * N.scale + B) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hSphereCompact : IsCompact N.central_sphere := by
    rw [N.central_sphere_eq]
    apply (isCompact_univ.prod isCompact_singleton).image_of_continuousOn
    apply N.coordinate_map_smooth.continuousOn.mono
    intro z hz
    have hz0 : z.2 = 0 := hz.2
    exact ⟨mem_univ _, hz0 ▸ ⟨neg_lt_zero.mpr hA, hA⟩⟩
  obtain ⟨gamma, h0, h1, hgamma, hlength⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hdist
  obtain ⟨t, ht, htS, hafter⟩ := Poincare.exists_last_visit_component
    hSphereCompact.isClosed zero_le_one hgamma.continuousOn
    (fun _ _ => mem_univ _) (by simpa only [h0] using N.center_on_central_sphere)
  have hcompl : (univ : Set M) \ N.central_sphere = N.central_sphereᶜ := by
    ext x
    simp
  have hpost (s : ℝ) (hs : s ∈ Ioc t 1) : gamma s ∈ P := by
    apply hcomponent q hq
    simpa only [hcompl, h1] using hafter s hs
  have hgammaV : MapsTo gamma (Icc t 1) (V : Set M) := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with heq | hlt
    · subst s
      exact hSV htS
    · exact hPV (hpost s ⟨hlt, hs.2⟩)
  have htail := intrinsicEDist_le_pathELength g ht.2
    (hgamma.mono (Icc_subset_Icc ht.1 le_rfl)) hgammaV
  rw [h1] at htail
  have htailBound : intrinsicEDist g (V : Set M) (gamma t) q ≤ ENNReal.ofReal B :=
    htail.trans ((Manifold.pathELength_mono ht.1 le_rfl).trans hlength.le)
  obtain ⟨alpha, ha0, ha1, halpha, hSphere, haLength, _, _⟩ :=
    exists_central_sphere_shortcut N N.center_on_central_sphere htS
  have hSphereDistance := intrinsicEDist_le_pathELength g zero_le_one halpha.contMDiffOn
    (fun s _ => hSV (hSphere (mem_univ s)))
  rw [ha0, ha1] at hSphereDistance
  have hpositive : 0 < (4 * standardSpherePathCeiling) * N.scale :=
    mul_pos (mul_pos (by norm_num) standardSpherePathCeiling_pos) N.scale_pos
  calc
    intrinsicEDist g (V : Set M) N.center q ≤
        intrinsicEDist g (V : Set M) N.center (gamma t) +
          intrinsicEDist g (V : Set M) (gamma t) q := intrinsicEDist_triangle_set _
    _ ≤ ENNReal.ofReal ((4 * standardSpherePathCeiling) * N.scale) +
        ENNReal.ofReal B := add_le_add (hSphereDistance.trans haLength.le) htailBound
    _ = ENNReal.ofReal ((4 * standardSpherePathCeiling) * N.scale + B) :=
      (ENNReal.ofReal_add hpositive.le hB.le).symm

end PoincareConjecture.M28
