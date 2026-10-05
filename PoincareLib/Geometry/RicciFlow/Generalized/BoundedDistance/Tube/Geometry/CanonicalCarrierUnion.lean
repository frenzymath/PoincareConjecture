import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.CapGeometry.CapScalarBand
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Cylinders.CylinderUniformScalar
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Persistence.CapTopology.NeckCollar

/-!
# The literal canonical carrier union in Claim 10.4

Only necks centered in the input set and caps whose actual cores meet it
contribute. Their literal union is open and connected. The actual cylinder
and cap scalar estimates put its high-scalar part back in the same scalar
superlevel component, as required by the relative cap barrier in
Morgan--Tian Claim 10.4, printed pp. 249--250, and Lemma A.2, p. 498.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

/-- The full strip of an actual epsilon-neck is preconnected; this is the
carrier input to the Claim 10.4 canonical union (Definition 2.18, p. 31). -/
theorem EpsilonNeck.isPreconnected_carrier (N : EpsilonNeck g) :
    IsPreconnected N.carrier := by
  have hfull : N.region (-N.epsilon⁻¹) N.epsilon⁻¹ = N.carrier := by
    ext x
    constructor
    · exact fun hx => hx.1
    · intro hx
      exact ⟨hx, (N.coordinate_inverse_mem x hx).2⟩
  rw [← hfull]
  exact N.isPreconnected_region le_rfl le_rfl

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

namespace ConnectedNeckCapCover

/-- The actual canonical carriers used by Claim 10.4. Unused input necks
and caps are excluded by the literal center/core intersection guards. -/
def canonicalCarrierUnion (H : ConnectedNeckCapCover g) : Set M :=
  {x | (∃ N ∈ H.necks, N.center ∈ H.X ∧ x ∈ N.carrier) ∨
    ∃ K ∈ H.caps, (K.core ∩ H.X).Nonempty ∧ x ∈ K.carrier}

/-- The actual center/core cover places the entire input set in its
literal carrier union (Claim 10.4, pp. 249--250). -/
theorem subset_canonicalCarrierUnion (H : ConnectedNeckCapCover g) :
    H.X ⊆ H.canonicalCarrierUnion := by
  intro x hx
  rcases H.pointwise_cover x hx with ⟨N, hN, hcenter⟩ | ⟨K, hK, hcore⟩
  · exact Or.inl ⟨N, hN, hcenter ▸ hx, hcenter ▸
      N.central_sphere_subset N.center_on_central_sphere⟩
  · exact Or.inr ⟨K, hK, ⟨x, hcore, hx⟩, K.core_subset_carrier_m28 hcore⟩

/-- The literal union is open because every contributing canonical carrier
is open (Claim 10.4, pp. 249--250). -/
theorem isOpen_canonicalCarrierUnion (H : ConnectedNeckCapCover g) :
    IsOpen H.canonicalCarrierUnion := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  rcases hx with ⟨N, hN, hcenter, hxN⟩ | ⟨K, hK, hcore, hxK⟩
  · exact Filter.mem_of_superset (N.carrier_open.mem_nhds hxN)
      (fun y hy => Or.inl ⟨N, hN, hcenter, hy⟩)
  · exact Filter.mem_of_superset (K.carrier_open.mem_nhds hxK)
      (fun y hy => Or.inr ⟨K, hK, hcore, hy⟩)

/-- Each contributing preconnected carrier meets the connected input set,
so its literal carrier union is connected (Claim 10.4, pp. 249--250). -/
theorem isConnected_canonicalCarrierUnion (H : ConnectedNeckCapCover g) :
    IsConnected H.canonicalCarrierUnion := by
  obtain ⟨x, hx⟩ := H.connected_X.nonempty
  refine ⟨⟨x, H.subset_canonicalCarrierUnion hx⟩, ?_⟩
  apply isPreconnected_of_forall x
  intro y hy
  rcases hy with ⟨N, hN, hcenter, hyN⟩ | ⟨K, hK, hcore, hyK⟩
  · have hcarrier : N.carrier ⊆ H.canonicalCarrierUnion :=
      fun z hz => Or.inl ⟨N, hN, hcenter, hz⟩
    refine ⟨H.X ∪ N.carrier,
      union_subset H.subset_canonicalCarrierUnion hcarrier, Or.inl hx, Or.inr hyN, ?_⟩
    exact H.connected_X.isPreconnected.union N.center hcenter
      (N.central_sphere_subset N.center_on_central_sphere) N.isPreconnected_carrier
  · have hcarrier : K.carrier ⊆ H.canonicalCarrierUnion :=
      fun z hz => Or.inr ⟨K, hK, hcore, hz⟩
    obtain ⟨z, hzcore, hzX⟩ := hcore
    refine ⟨H.X ∪ K.carrier,
      union_subset H.subset_canonicalCarrierUnion hcarrier, Or.inl hx, Or.inr hyK, ?_⟩
    exact H.connected_X.isPreconnected.union z hzX (K.core_subset_carrier_m28 hzcore)
      K.isPreconnected_carrier

end ConnectedNeckCapCover

namespace M28

/-- One universal accuracy puts the high-scalar part of the actual
canonical carrier union back in its input superlevel component. Both scalar
ratios are derived from the frozen certificates (Claim 10.4, pp. 249--250). -/
theorem exists_canonicalCarrierUnion_scalar_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] (g : RiemannianMetric 3 M)
        (D : LeviCivitaData g) (H : ConnectedNeckCapCover g) (Q : ℝ) (z : M),
        0 < Q → H.epsilon ≤ epsilon₀ →
        H.X = connectedComponentIn {p | 4 * Q < D.scalarCurvature p} z →
        ∀ w ∈ H.canonicalCarrierUnion,
          8 * (max H.cap_constant 2) * Q ≤ D.scalarCurvature w → w ∈ H.X := by
  obtain ⟨epsilon₀, hepsilon₀, hthreshold, hneck⟩ :=
    tube.exists_cylinder_scalar_ratio_accuracy.{u}
  refine ⟨epsilon₀, hepsilon₀, hthreshold, ?_⟩
  intro M _ _ _ _ _ _ _ g D H Q z hQ hsmall hX w hw hlow
  let B := max H.cap_constant 2
  have hB : 2 ≤ B := le_max_right H.cap_constant 2
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hBQ : 0 < B * Q := mul_pos hBpos hQ
  have hQle : 2 * Q ≤ B * Q := mul_le_mul_of_nonneg_right hB hQ.le
  have hlow' : 8 * B * Q ≤ D.scalarCurvature w := hlow
  rcases hw with ⟨N, hN, hcenter, hwN⟩ | ⟨K, hK, hcore, hwK⟩
  · have hcenterN : N.center ∈ N.carrier :=
      N.central_sphere_subset N.center_on_central_sphere
    have hepsilon : N.epsilon ≤ epsilon₀ := (H.neck_epsilon N hN) ▸ hsmall
    have hsuper : N.carrier ⊆ {p | 4 * Q < D.scalarCurvature p} := by
      intro p hp
      have hratio := hneck M g D N hepsilon w hwN p hp
      change 4 * Q < D.scalarCurvature p
      nlinarith only [hlow', hratio, hQ, hQle]
    have hcontain := N.isPreconnected_carrier.subset_connectedComponentIn hcenterN hsuper
    have hcomp := connectedComponentIn_eq (hX ▸ hcenter)
    rw [← hcomp, ← hX] at hcontain
    exact hcontain hwN
  · obtain ⟨p, hpCore, hpX⟩ := hcore
    have hpK : p ∈ K.carrier := K.core_subset_carrier_m28 hpCore
    have hbound : K.cap_constant ≤ B :=
      (H.cap_constant_bound K hK).trans (le_max_left H.cap_constant 2)
    have hsuper : K.carrier ⊆ {p | 4 * Q < D.scalarCurvature p} := by
      intro q hq
      have hratio := K.scalar_lt_mul D hbound hq hwK
      have hmul : B * (4 * Q) < B * D.scalarCurvature q := by
        nlinarith only [hlow', hratio, hBQ]
      exact (mul_lt_mul_iff_right₀ hBpos).mp hmul
    have hcontain := K.isPreconnected_carrier.subset_connectedComponentIn hpK hsuper
    have hcomp := connectedComponentIn_eq (hX ▸ hpX)
    rw [← hcomp, ← hX] at hcontain
    exact hcontain hwK

end M28
end PoincareMT
