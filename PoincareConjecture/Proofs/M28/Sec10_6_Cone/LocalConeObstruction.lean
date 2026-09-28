import PoincareConjecture.Proofs.M28.Sec10_6_Cone.OpenConePotential
import PoincareConjecture.Proofs.M28.Sec10_6_Cone.ChordConeAnnulus
import PoincareConjecture.Proofs.M28.Sec10_6_Cone.TerminalQuadratic
import PoincareConjecture.Proofs.M03.ConnectionExistence
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Pullback










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology NNReal

universe u v

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {L : Type v} [MetricSpace L]





theorem no_positive_terminal_scalar_of_chord_annulus_embedding
    (P : RicciFlowCurvatureTheory.{u}) {t0 t1 : ℝ} (htime : t0 < t1)
    (F : RicciFlow 3 M (Icc t0 t1))
    (hoperator : ∀ t ∈ Icc t0 t1, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (htriangle : ∀ x y z : L, ∀ r s t : ℝ, 0 < r → 0 < s → 0 < t →
      chordConeDistance r t (dist x z) ≤
        chordConeDistance r s (dist x y) + chordConeDistance s t (dist y z))
    (K : Set M) (V : TopologicalSpace.Opens M) (hVK : (V : Set M) ⊆ K)
    (jK : K → ChordConeAnnulus L a b) :
    letI := chordConeAnnulusMetric ha hab htriangle
    (∀ x y : K, edist (jK x) (jK y) = (F.metric t1).edist (x : M) (y : M)) →
    (∀ x : K, ((jK x).2 : ℝ) ∈ Ioo a b) →
    ∀ p : V, 0 < (F.connection t1).scalarCurvature (p : M) → False := by
  let := chordConeAnnulusMetric ha hab htriangle
  intro hmetric hmargin p hscalar
  let D (t : ℝ) : LeviCivitaData (intrinsicOpenMetric (F.metric t) V) :=
    Classical.choice (exists_leviCivitaData (intrinsicOpenMetric (F.metric t) V))
  let G : RicciFlow 3 V (Icc t0 t1) :=
    F.pullbackWithConnection (Subtype.val : V → M)
      (openSubtype_isLocalDiffeomorph V) D
  have hinclusion : ContMDiff (𝓡 3) (𝓡 3) ∞ (Subtype.val : V → M) :=
    contMDiff_subtype_val
  have hoperatorG : ∀ t ∈ Icc t0 t1, ∀ x : V,
      (G.connection t).NonnegativeCurvatureOperator x := by
    intro t ht x
    apply ((G.connection t).nonnegativeCurvatureOperator_iff_of_local_isometry
      (F.connection t) (f := (Subtype.val : V → M)) isOpen_univ
      hinclusion.contMDiffOn (fun _ _ _ _ => rfl) (mem_univ x)).mpr
    exact hoperator t ht (x : M)
  have hscalarG : 0 < (G.connection t1).scalarCurvature p := by
    have hread := (G.connection t1).scalarCurvature_eq_of_local_isometry
      (F.connection t1) (f := (Subtype.val : V → M)) isOpen_univ
      hinclusion.contMDiffOn (fun _ _ _ _ => rfl) (mem_univ p)
    exact hread.symm ▸ hscalar
  let B : ℝ≥0 := ⟨b, (ha.trans_le hab).le⟩
  have hbound (x : ChordConeAnnulus L a b) : |(x.2 : ℝ)| ≤ (B : ℝ) := by
    rw [abs_of_nonneg (ha.le.trans x.2.property.1)]
    exact x.2.property.2
  have hvariation :
      let j : V → ChordConeAnnulus L a b := fun x => jK ⟨x, hVK x.property⟩
      ∀ x z y : V, ∀ᶠ c : ℝ in 𝓝 1, ∃ w : ChordConeAnnulus L a b,
        dist (j x) w ^ 2 = c ^ 2 * ((j z).2 : ℝ) ^ 2 + ((j x).2 : ℝ) ^ 2 -
          c * (((j z).2 : ℝ) ^ 2 + ((j x).2 : ℝ) ^ 2 - dist (j x) (j z) ^ 2) ∧
        dist (j y) w ^ 2 = c ^ 2 * ((j z).2 : ℝ) ^ 2 + ((j y).2 : ℝ) ^ 2 -
          c * (((j z).2 : ℝ) ^ 2 + ((j y).2 : ℝ) ^ 2 - dist (j y) (j z) ^ 2) := by
    intro j x z y
    exact chordConeAnnulus_local_radial_variation ha hab htriangle
      (j x) (j z) (j y) (hmargin ⟨z, hVK z.property⟩)
  obtain ⟨hLip, hquad, _hsmooth⟩ := open_radius_potential_of_retained_isometry
    (F.metric t1) K V hVK jK hmetric (fun x => (x.2 : ℝ))
    (chordConeAnnulus_radius_lipschitz ha hab htriangle) hbound hvariation
  exact no_positive_terminal_scalar_of_quadratic_potential P htime G hoperatorG
    (fun x : V => ((jK ⟨x, hVK x.property⟩).2 : ℝ) ^ 2 / 2)
    hLip hquad p hscalarG

end PoincareConjecture.M28
