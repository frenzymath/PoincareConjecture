import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapRatio
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RelativeCapBarrier










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.CapCertificate

open M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

omit [T2Space M] in


theorem isPreconnected_carrier (N : CapCertificate g) : IsPreconnected N.carrier := by
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  have hd : intrinsicEDist g N.carrier x y ≤ intrinsicDiameter g N.carrier :=
    le_sSup ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  obtain ⟨γ, h0, h1, hγ, hγN, _⟩ :=
    exists_intrinsic_competitor g (hd.trans_lt N.intrinsic_diameter_bound)
  refine ⟨γ '' Icc (0 : ℝ) 1, ?_, ?_, ?_,
    isPreconnected_Icc.image γ hγ.continuousOn⟩
  · rintro z ⟨t, ht, rfl⟩
    exact hγN ht
  · exact ⟨0, by simp, h0⟩
  · exact ⟨1, by simp, h1⟩

omit [T2Space M] in



theorem carrier_subset_scalar_component (N : CapCertificate g) (D : LeviCivitaData g)
    {B Q : ℝ} (hB : N.cap_constant ≤ B) (hQ : 0 < Q)
    {w : M} (hw : w ∈ N.carrier) (hlow : 16 * B * Q ≤ D.scalarCurvature w) :
    N.carrier ⊆ connectedComponentIn {p : M | 4 * Q < D.scalarCurvature p} w := by
  have hBpos : 0 < B := zero_lt_one.trans (N.one_lt_cap_constant_m28.trans_le hB)
  apply N.isPreconnected_carrier.subset_connectedComponentIn hw
  intro p hp
  have hscalar : 16 * Q < D.scalarCurvature p := by
    have hcmp : B * (16 * Q) < B * D.scalarCurvature p := by
      calc
        B * (16 * Q) = 16 * B * Q := by ring
        _ ≤ D.scalarCurvature w := hlow
        _ < B * D.scalarCurvature p := N.scalar_lt_mul D hB hp hw
    exact (mul_lt_mul_iff_right₀ hBpos).mp hcmp
  exact lt_trans (by linarith only [hQ]) hscalar

omit [T2Space M] in


theorem endpoints_not_mem_of_scalar_band (N : CapCertificate g) (D : LeviCivitaData g)
    {B Q : ℝ} (hB : N.cap_constant ≤ B) (hQ : 0 < Q)
    {z y w : M} (hw : w ∈ N.carrier)
    (hz : D.scalarCurvature z ≤ 8 * Q)
    (hlow : 16 * B * Q ≤ D.scalarCurvature w)
    (hhigh : D.scalarCurvature w ≤ D.scalarCurvature y / (2 * B)) :
    z ∉ N.carrier ∧ y ∉ N.carrier := by
  have hBpos : 0 < B := zero_lt_one.trans (N.one_lt_cap_constant_m28.trans_le hB)
  constructor
  · intro hzN
    have hratio := N.scalar_lt_mul D hB hzN hw
    have hzbound := mul_le_mul_of_nonneg_left hz hBpos.le
    have hBQ : 0 < B * Q := mul_pos hBpos hQ
    nlinarith only [hratio, hzbound, hlow, hBQ]
  · intro hyN
    have hratio := N.scalar_lt_mul D hB hw hyN
    have hupper := (le_div_iff₀ (mul_pos (by norm_num) hBpos)).mp hhigh
    have hpositive : 0 < B * D.scalarCurvature w :=
      mul_pos hBpos (N.scalar_pos_of_connection D hw)
    nlinarith only [hratio, hupper, hpositive]




theorem not_mem_core_of_scalar_band (N : CapCertificate g) (D : LeviCivitaData g)
    (hepsilon : N.epsilon ≤ neckShorteningEpsilon)
    {B Q : ℝ} (hB : N.cap_constant ≤ B) (hQ : 0 < Q)
    {U : Set M} {γ : ℝ → M} {a b t : ℝ} (ht : t ∈ Icc a b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U)
    (hfinite : g.pathELength γ a b ≠ ⊤)
    (hmin : g.pathELength γ a b = intrinsicEDist g U (γ a) (γ b))
    (hcomponent : connectedComponentIn {p : M | 4 * Q < D.scalarCurvature p} (γ t) ⊆ U)
    (hstart : D.scalarCurvature (γ a) ≤ 8 * Q)
    (hlow : 16 * B * Q ≤ D.scalarCurvature (γ t))
    (hhigh : D.scalarCurvature (γ t) ≤ D.scalarCurvature (γ b) / (2 * B)) :
    γ t ∉ N.core := by
  intro hcore
  have hw := N.core_subset_carrier_m28 hcore
  have hNU : N.carrier ⊆ U :=
    (N.carrier_subset_scalar_component D hB hQ hw hlow).trans hcomponent
  have hendpoints := N.endpoints_not_mem_of_scalar_band D hB hQ hw hstart hlow hhigh
  have hclosed : γ t ∈ N.closed_core := by
    rw [N.core_eq_interior_closed_core] at hcore
    exact interior_subset hcore
  rcases N.endpoint_mem_of_intrinsic_minimizer hepsilon hNU ht hγ hγU hfinite hmin
    hclosed with ha | hb
  · exact hendpoints.1 ha
  · exact hendpoints.2 hb

end PoincareConjecture.CapCertificate
