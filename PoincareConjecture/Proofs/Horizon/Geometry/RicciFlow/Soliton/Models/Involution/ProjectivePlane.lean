import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Cylinder
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Transitions
import PoincareConjecture.Proofs.Horizon.Topology.Quotient.Coordinates







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.QuotientSphereLineCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} {G : ShrinkingSolitonFlow S}


theorem quotient_map_localDiffeomorph (q : QuotientSphereLineCertificate G) :
    letI := q.cover_topology
    letI := q.cover_charted
    letI := q.cover_manifold
    letI := q.product.surface_topology
    letI := q.product.product_charted
    letI := q.product.product_manifold
    letI := q.quotient_topology
    letI := q.quotient_charted
    letI := q.quotient_manifold
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q.quotient_map := by
  let := q.cover_topology
  let := q.cover_charted
  let := q.cover_manifold
  let := q.product.surface_topology
  let := q.product.product_charted
  let := q.product.product_manifold
  let := q.quotient_topology
  let := q.quotient_charted
  let := q.quotient_manifold
  apply Poincare.isLocalDiffeomorph_of_contMDiff_bijective_mfderiv q.quotient_map_smooth
  intro p
  exact (q.product.product_metric (-1)).mfderiv_bijective_of_pullback_eq
    (q.quotient_metric (-1)) p
    (fun v w ↦ (q.quotient_metric_pullback (-1) (by norm_num) p v w).symm)


theorem quotient_map_isOpenQuotientMap (q : QuotientSphereLineCertificate G) :
    letI := q.cover_topology
    letI := q.cover_charted
    letI := q.cover_manifold
    letI := q.product.surface_topology
    letI := q.product.product_charted
    letI := q.product.product_manifold
    letI := q.quotient_topology
    letI := q.quotient_charted
    letI := q.quotient_manifold
    IsOpenQuotientMap q.quotient_map := by
  let := q.cover_topology
  let := q.cover_charted
  let := q.cover_manifold
  let := q.product.surface_topology
  let := q.product.product_charted
  let := q.product.product_manifold
  let := q.quotient_topology
  let := q.quotient_charted
  let := q.quotient_manifold
  exact ⟨q.quotient_map_surjective, q.quotient_map_smooth.continuous,
    q.quotient_map_localDiffeomorph.isOpenMap⟩




theorem exists_projectivePlaneCoordinates (r : Setoid UnitTwoSphere)
    (hr : ∀ x y, r x y ↔ x = y ∨ x = -y)
    (q : QuotientSphereLineCertificate G) :
    letI := q.cover_topology
    letI := q.cover_charted
    letI := q.cover_manifold
    letI := q.product.surface_topology
    letI := q.product.surface_charted
    letI := q.product.surface_manifold
    letI := q.product.product_charted
    letI := q.product.product_manifold
    letI := q.quotient_topology
    letI := q.quotient_charted
    letI := q.quotient_manifold
    (∀ p : q.product.surface × ℝ,
      q.involution p = (q.product.surface_sphere.symm (-(q.product.surface_sphere p.1)), p.2)) →
    ∃ e : q.quotient_carrier ≃ₜ (Quotient r × ℝ), ∀ p : q.product.surface × ℝ,
      e (q.quotient_map p) = (Quotient.mk r (q.product.surface_sphere p.1), p.2) := by
  let := q.cover_topology
  let := q.cover_charted
  let := q.cover_manifold
  let := q.product.surface_topology
  let := q.product.surface_charted
  let := q.product.surface_manifold
  let := q.product.product_charted
  let := q.product.product_manifold
  let := q.quotient_topology
  let := q.quotient_charted
  let := q.quotient_manifold
  intro hformula
  let E : q.product.surface × ℝ ≃ₜ UnitTwoSphere × ℝ :=
    q.product.surface_sphere.toHomeomorph.prodCongr (Homeomorph.refl ℝ)
  let proj : UnitTwoSphere × ℝ → Quotient r × ℝ := Prod.map (Quotient.mk r) id
  have hproj : IsOpenQuotientMap proj :=
    (Poincare.Topology.isOpenQuotientMap_of_pair_fibers r Neg.neg continuous_neg hr).prodMap
      IsOpenQuotientMap.id
  have hc : IsOpenQuotientMap (proj ∘ E) := hproj.comp E.isOpenQuotientMap
  let f : C(q.product.surface × ℝ, q.quotient_carrier) :=
    ⟨q.quotient_map, q.quotient_map_smooth.continuous⟩
  let c : C(q.product.surface × ℝ, Quotient r × ℝ) := ⟨proj ∘ E, hc.continuous⟩
  have hf : Topology.IsQuotientMap f := q.quotient_map_isOpenQuotientMap.isQuotientMap
  have hcf : ∀ p p', f p = f p' ↔ c p = c p' := by
    intro p p'
    change q.quotient_map p = q.quotient_map p' ↔
      (Quotient.mk r (q.product.surface_sphere p.1), p.2) =
        (Quotient.mk r (q.product.surface_sphere p'.1), p'.2)
    rw [q.quotient_fiber_eq_orbit, hformula p]
    constructor
    · rintro (rfl | rfl)
      · rfl
      · apply Prod.ext
        · apply Quotient.sound
          apply (hr _ _).mpr
          right
          simp
        · rfl
    · intro h
      have hs := Quotient.exact (congrArg Prod.fst h)
      have hl := congrArg Prod.snd h
      rcases (hr _ _).mp hs with hs | hs
      · left
        exact Prod.ext (q.product.surface_sphere.injective hs.symm) hl.symm
      · right
        apply Prod.ext
        · apply q.product.surface_sphere.injective
          rw [hs]
          simp
        · exact hl.symm
  refine ⟨hf.homeomorphOfFibers hc.isQuotientMap hcf, ?_⟩
  intro p
  exact hf.homeomorphOfFibers_apply hc.isQuotientMap hcf p

end PoincareConjecture.QuotientSphereLineCertificate
