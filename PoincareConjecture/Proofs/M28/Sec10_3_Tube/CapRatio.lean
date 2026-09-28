import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Uniqueness

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem LeviCivitaData.scalarCurvature_eq_m28 {g : RiemannianMetric n M}
    (D D' : LeviCivitaData g) (x : M) :
    D.scalarCurvature x = D'.scalarCurvature x := by
  simp only [LeviCivitaData.scalarCurvature, LeviCivitaData.ricci,
    D.curvatureTensor_eq D']

end PoincareConjecture

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem core_subset_carrier_m28 (N : CapCertificate g) : N.core ⊆ N.carrier := by
  rw [N.core_eq_interior_closed_core]
  exact interior_subset.trans (by rw [N.closed_core_eq_complement_end]; exact sdiff_subset)

theorem one_lt_cap_constant_m28 (N : CapCertificate g) : 1 < N.cap_constant := by
  obtain ⟨x, hx⟩ := N.core_nonempty
  have hxN := N.core_subset_carrier_m28 hx
  obtain ⟨b, hb, hratio⟩ := N.scalar_ratio
  have hself := hratio x hxN x hxN
  have hpos := N.scalar_pos x hxN
  have hbone : 1 ≤ b := by nlinarith
  exact hbone.trans_lt hb

theorem scalar_pos_of_connection (N : CapCertificate g) (D : LeviCivitaData g)
    {x : M} (hx : x ∈ N.carrier) : 0 < D.scalarCurvature x := by
  rw [← N.connection.scalarCurvature_eq_m28 D x]
  exact N.scalar_pos x hx

theorem scalar_lt_cap_constant_mul (N : CapCertificate g) (D : LeviCivitaData g)
    {x y : M} (hx : x ∈ N.carrier) (hy : y ∈ N.carrier) :
    D.scalarCurvature y < N.cap_constant * D.scalarCurvature x := by
  obtain ⟨b, hb, hratio⟩ := N.scalar_ratio
  rw [← N.connection.scalarCurvature_eq_m28 D x, ← N.connection.scalarCurvature_eq_m28 D y]
  exact (hratio x hx y hy).trans_lt (mul_lt_mul_of_pos_right hb (N.scalar_pos x hx))

theorem scalar_lt_mul (N : CapCertificate g) (D : LeviCivitaData g)
    {C : ℝ} (hC : N.cap_constant ≤ C)
    {x y : M} (hx : x ∈ N.carrier) (hy : y ∈ N.carrier) :
    D.scalarCurvature y < C * D.scalarCurvature x :=
  (N.scalar_lt_cap_constant_mul D hx hy).trans_le
    (mul_le_mul_of_nonneg_right hC (N.scalar_pos_of_connection D hx).le)

theorem inter_nonempty_of_preconnected_union (N N' : CapCertificate g)
    (hconn : IsPreconnected (N.carrier ∪ N'.carrier)) :
    (N.carrier ∩ N'.carrier).Nonempty := by
  obtain ⟨x, hx⟩ := N.core_nonempty
  obtain ⟨y, hy⟩ := N'.core_nonempty
  have hxN := N.core_subset_carrier_m28 hx
  have hyN := N'.core_subset_carrier_m28 hy
  obtain ⟨z, _, hz⟩ := hconn N.carrier N'.carrier N.carrier_open N'.carrier_open
    Subset.rfl ⟨x, Or.inl hxN, hxN⟩ ⟨y, Or.inr hyN, hyN⟩
  exact ⟨z, hz⟩

theorem scalar_le_sq_mul_on_union (N N' : CapCertificate g) (D : LeviCivitaData g)
    {C : ℝ} (hC : N.cap_constant ≤ C) (hC' : N'.cap_constant ≤ C)
    (hoverlap : (N.carrier ∩ N'.carrier).Nonempty)
    {x y : M} (hx : x ∈ N.carrier ∪ N'.carrier)
    (hy : y ∈ N.carrier ∪ N'.carrier) :
    D.scalarCurvature y ≤ C ^ 2 * D.scalarCurvature x := by
  have hCone : 1 < C := N.one_lt_cap_constant_m28.trans_le hC
  have hCpos : 0 < C := lt_trans zero_lt_one hCone
  obtain ⟨z, hz, hz'⟩ := hoverlap
  have hsame (K : CapCertificate g) (hK : K.cap_constant ≤ C)
      {a b : M} (ha : a ∈ K.carrier) (hb : b ∈ K.carrier) :
      D.scalarCurvature b ≤ C ^ 2 * D.scalarCurvature a := by
    have hpos := K.scalar_pos_of_connection D ha
    have hsq : C ≤ C ^ 2 := by nlinarith
    exact (K.scalar_lt_mul D hK ha hb).le.trans (mul_le_mul_of_nonneg_right hsq hpos.le)
  have hcross (K L : CapCertificate g) (hK : K.cap_constant ≤ C)
      (hL : L.cap_constant ≤ C) (hzK : z ∈ K.carrier) (hzL : z ∈ L.carrier)
      {a b : M} (ha : a ∈ K.carrier) (hb : b ∈ L.carrier) :
      D.scalarCurvature b ≤ C ^ 2 * D.scalarCurvature a := by
    calc
      D.scalarCurvature b ≤ C * D.scalarCurvature z := (L.scalar_lt_mul D hL hzL hb).le
      _ ≤ C * (C * D.scalarCurvature a) :=
        mul_le_mul_of_nonneg_left (K.scalar_lt_mul D hK ha hzK).le hCpos.le
      _ = C ^ 2 * D.scalarCurvature a := by ring
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hsame N hC hx hy
  · exact hcross N N' hC hC' hz hz' hx hy
  · exact hcross N' N hC' hC hz' hz hx hy
  · exact hsame N' hC' hx hy

end PoincareConjecture.CapCertificate
