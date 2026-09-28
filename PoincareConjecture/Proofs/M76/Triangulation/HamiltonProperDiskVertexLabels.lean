import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexSigns
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskBaseFaces
import PoincareConjecture.Proofs.M76.Mathlib.InteriorFullCofaces

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (V2 × ℝ)
local notation "Cube" => closedBall (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : Cube ≃ₜ D}

theorem HamiltonProperDiskTriangulation.exists_vertex_normal_label
    (T : HamiltonProperDiskTriangulation R D b) (hb : b.IsFinitePL)
    (p : T.disk.vertices) (c : E ≃ᴬ[ℝ] V) :
    ∃ δ : ℝ, δ ≠ 0 ∧
      ∀ (s u : Finset E) (_hs : s ∈ T.disk.faces), s.card = 3 → (p : E) ∈ s →
        u ∈ T.ambient.faces → u.card = 4 → s ⊆ u →
        ∀ (P : V2 →ᴬ[ℝ] E), Function.Injective P →
          (∀ x ∈ convexHull ℝ (s : Set E), P (T.inverse x) = x) →
          ∀ w ∈ convexHull ℝ (u : Set E), ((T.pairChart p).chart w).2 ≠ 0 →
            0 < affineDiskNormal (c.toAffineEquiv.toAffineMap.comp P.toAffineMap) (c w) *
              (δ * ((T.pairChart p).chart w).2) := by
  classical
  let H := (T.pairChart p).chart
  have hpface : {(p : E)} ∈ T.disk.faces := p.property
  obtain ⟨s0, hs0, hps0, hsc0⟩ := T.exists_disk_triangle_coface hpface
  have hps : (p : E) ∈ s0 := hps0 (Finset.mem_singleton_self _)
  have hs0star : s0 ∈ (T.ambient.closedStar p).faces :=
    ⟨T.disk_le hs0, by simpa only [Finset.insert_eq_of_mem hps] using T.disk_le hs0⟩
  have hpH : (p : E) ∈ H.source := T.star_source p
    ((T.ambient.closedStar p).subset_space hs0star hps)
  have hpD : (p : E) ∈ D := T.disk_space.subset (T.disk.vertices_subset_space p.property)
  have hpR : (p : E) ∈ R := by
    rcases (T.pairChart p).model with ⟨hinside, _⟩ | ⟨hregion, hdisk⟩
    · exact interior_subset (hinside hpH)
    · exact (hregion p hpH).mpr ((hdisk p hpH).mp hpD).1
  have hdim : Module.finrank ℝ E = 3 := by
    simpa [Module.finrank_prod] using c.toAffineEquiv.linear.finrank_eq
  obtain ⟨u0, hu0, hsu0, huc0⟩ :=
    T.ambient.exists_full_coface_of_hull_meets_interior T.finite (T.disk_le hs0)
      ⟨p, subset_convexHull ℝ _ hps, T.region_interior hpR⟩
  have hucard : u0.card = 4 := by simpa [hdim] using huc0
  obtain ⟨P0, hP0i, hP0, _, _⟩ := T.exists_original_triangle_parameter hs0 hsc0
  obtain ⟨A, B, hA, _⟩ := T.exists_incident_affine_chart_formulas p c
    hs0 hsc0 hps hu0 hucard hsu0 P0 hP0i hP0
  have hwexists : ∃ w ∈ convexHull ℝ (u0 : Set E), (H w).2 ≠ 0 := by
    by_contra! hn
    let a : E →ᵃ[ℝ] ℝ := (LinearMap.snd ℝ V2 ℝ).toAffineMap.comp
      (A.toAffineMap.comp c.toAffineEquiv.toAffineMap)
    have hspan : affineSpan ℝ (u0 : Set E) = ⊤ := by
      simpa using ((T.ambient.indep hu0).affineBasisOfCard huc0).tot
    have heq : EqOn a (AffineMap.const ℝ E (0 : ℝ)) (u0 : Set E) := by
      intro x hx
      change (A (c x)).2 = 0
      rw [hA x (subset_convexHull ℝ _ hx)]
      exact hn x (subset_convexHull ℝ _ hx)
    have ha : a = AffineMap.const ℝ E (0 : ℝ) := AffineMap.ext_on hspan heq
    have h := congrArg (fun f : E →ᵃ[ℝ] ℝ => f (c.symm (A.symm (0, 1)))) ha
    change (A (c (c.symm (A.symm (0, 1))))).2 = 0 at h
    rw [c.apply_symm_apply, A.apply_symm_apply] at h
    norm_num at h
  obtain ⟨w0, hw0, hheight⟩ := hwexists
  let n0 := affineDiskNormal (c.toAffineEquiv.toAffineMap.comp P0.toAffineMap) (c w0)
  have hn0pos : 0 < n0 * n0 := T.normal_mul_pos_at_vertex hb p c
    hs0 hs0 hsc0 hsc0 hps hps hu0 hu0 hucard hucard hsu0 hsu0
    P0 P0 hP0i hP0i hP0 hP0 hw0 hw0 (mul_self_pos.mpr hheight)
  have hn0 : n0 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hn0pos
    exact lt_irrefl _ hn0pos
  let δ := n0 * (H w0).2
  refine ⟨δ, mul_ne_zero hn0 hheight, ?_⟩
  intro s u hs hsc hp hu huc hsu P hPi hP w hw hH
  obtain ⟨α, β, hα, hβ, he⟩ := T.normal_product_equation_at_vertex hb p c
    hs0 hs hsc0 hsc hps hp hu0 hu hucard huc hsu0 hsu
    P0 P hP0i hPi hP0 hP hw0 hw
  let n := affineDiskNormal (c.toAffineEquiv.toAffineMap.comp P.toAffineMap) (c w)
  have he' : (n * (δ * (H w).2)) * α = β * (((H w0).2 * (H w).2) ^ 2) := by
    calc
      _ = (n0 * n * α) * ((H w0).2 * (H w).2) := by dsimp [δ]; ring
      _ = (β * ((H w0).2 * (H w).2)) * ((H w0).2 * (H w).2) := by rw [he]
      _ = _ := by ring
  apply (mul_pos_iff_of_pos_right hα).mp
  rw [he']
  exact mul_pos hβ (sq_pos_of_ne_zero (mul_ne_zero hheight hH))

end PoincareConjecture.M76.HamiltonIndexOne
