import PoincareConjecture.Proofs.M76.Mathlib.CertifiedDirectionalIsotopy
import PoincareConjecture.Proofs.M76.Mathlib.GeometricBandLevelCharts
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages










set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem IsFinitePL.exists_prescribed_cap_collar_isotopy
    {B T d b U : Set E} {upper r : E → ℝ} (hupper : ∀ x ∈ B, 0 ≤ upper x)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (hdplane : d ⊆ {x | A x = 0})
    (hr : FinitePiecewiseAffineOn r d) (hrnonneg : ∀ x ∈ d, 0 ≤ r x)
    (v : E) (hv : A.linear v = 1) (Q : SimplicialComplex ℝ E) (hQ : Q.faces.Finite)
    (hrQ : ∀ x ∈ d ∩ Q.space, r x = 0) (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ f : E × ℝ → E, (∀ p, (C p : E) = f p) ∧
      ∃ g : E → ℝ, FinitePiecewiseAffineOn g T ∧ (∀ x, 0 ≤ g x) ∧
        EqOn g r d ∧ (∀ x ∈ Q.space, g x = 0) ∧ (∀ x, x ∉ U → g x = 0) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
          (∀ (t : Icc (-ε) ε) (L : SimplicialComplex ℝ E), L.faces.Finite →
            FinitePiecewiseAffineOn (H t : E → E) L.space) ∧
          Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
          Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
          (∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v) ∧
          ∀ t : Icc (-ε) ε,
            FinitePiecewiseAffineOn (H t : E → E) d ∧
            FinitePiecewiseAffineOn (H t : E → E) T ∧
            (∀ x ∈ d, A (H t x) = (t : ℝ) * r x) ∧
            IsFinitePLBallPair (ℝ × ℝ) (H t '' d) (H t '' b) ∧
            ∀ c : ℝ,
              ∃ L : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g (f (x, 0)))
                  (upper x + (t : ℝ) * g (f (x, upper x)))} ≃ₜ
                  ((H t '' T) ∩ {x | A x = c} : Set E), L.IsFinitePL ∧
                ∀ x : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g (f (x, 0)))
                    (upper x + (t : ℝ) * g (f (x, upper x)))},
                  ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
                    (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H t (C p) ∧
                    ((t : ℝ) * g (f (x, 0)) = c ↔ (p : E × ℝ).2 = 0) ∧
                    (upper x + (t : ℝ) * g (f (x, upper x)) = c ↔
                      (p : E × ℝ).2 = upper x) := by
  obtain ⟨f, hf, hfval⟩ := hC
  have hCPL : C.IsFinitePL := ⟨f, hf, hfval⟩
  obtain ⟨_, ⟨JT, hJT, hJTs, _⟩, _⟩ := hCPL.symm
  have hTc : IsCompact T := hJTs ▸ JT.isCompact_space_of_finite hJT
  obtain ⟨g, hgn, hgr, hgQ, hgU, ε₀, hε₀, H₀, hc₀, hci₀, hformula,
      R, hR, _, hcover, hgR, _, hPL, hglobal⟩ :=
    hr.exists_certified_directional_isotopy_with_global_finitePL
      hrnonneg A v hv Q hQ hrQ hU hdU hTc
  have hdR : d ⊆ R.space :=
    (subset_union_left.trans (subset_union_left.trans hcover)).trans interior_subset
  have hTR : T ⊆ R.space := (subset_union_right.trans hcover).trans interior_subset
  have hgT : FinitePiecewiseAffineOn g T := by
    rw [← hJTs]
    exact hgR.restrict JT hJT (hJTs.subset.trans hTR)
  obtain ⟨δ, hδ, hlevels⟩ :=
    hf.exists_geometric_band_level_charts hupper C hfval A hheight hgT v hv
  let ε := min ε₀ (δ / 2)
  have hε : 0 < ε := lt_min hε₀ (half_pos hδ)
  have hεle : ε ≤ ε₀ := min_le_left _ _
  have hεδ : ε < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  let embed : Icc (-ε) ε → Icc (-ε₀) ε₀ := fun t =>
    ⟨t, (neg_le_neg hεle).trans t.property.1, t.property.2.trans hεle⟩
  have hembed : Continuous embed := continuous_subtype_val.subtype_mk _
  let H : Icc (-ε) ε → E ≃ₜ E := fun t => H₀ (embed t)
  have hHval (t : Icc (-ε) ε) (x : E) : H t x = x + ((t : ℝ) * g x) • v :=
    hformula (embed t) x
  have htδ (t : Icc (-ε) ε) : |(t : ℝ)| < δ :=
    (abs_le.mpr t.property).trans_lt hεδ
  have hcopy := hr
  obtain ⟨Jd, hJd, hJds, _⟩ := hcopy
  refine ⟨f, hfval, g, hgT, hgn, hgr, hgQ, hgU,
    ε, hε, H, (fun t L hL => hglobal (embed t) L hL), ?_, ?_, hHval, fun t => ?_⟩
  · exact hc₀.comp ((hembed.comp continuous_fst).prodMk continuous_snd)
  · exact hci₀.comp ((hembed.comp continuous_fst).prodMk continuous_snd)
  · have hHd : FinitePiecewiseAffineOn (H t : E → E) d := by
      rw [← hJds]
      exact (hPL (embed t)).restrict Jd hJd (hJds.subset.trans hdR)
    have hHT : FinitePiecewiseAffineOn (H t : E → E) T := by
      rw [← hJTs]
      exact (hPL (embed t)).restrict JT hJT (hJTs.subset.trans hTR)
    refine ⟨hHd, hHT, ?_, hd.image hHd (H t).injective.injOn, ?_⟩
    · intro x hx
      rw [hHval, hgr hx, add_comm x]
      change A (((t : ℝ) * r x) • v +ᵥ x) = (t : ℝ) * r x
      rw [A.map_vadd, map_smul, hv]
      change (t : ℝ) * r x * 1 + A x = (t : ℝ) * r x
      rw [hdplane hx, mul_one, add_zero]
    · intro c
      obtain ⟨L, hL, hLp⟩ := hlevels t (htδ t) (H t) hHT (fun x _ => hHval t x) c
      have hdomain : {x : E | x ∈ B ∧ c ∈ Icc (0 + (t : ℝ) * g (f (x, 0)))
          (upper x + (t : ℝ) * g (f (x, upper x)))} =
          {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g (f (x, 0)))
            (upper x + (t : ℝ) * g (f (x, upper x)))} := by
        ext x
        simp only [zero_add]
      let G := (Homeomorph.setCongr hdomain.symm).trans
        (L.trans (Homeomorph.setCongr rfl))
      refine ⟨G, hL.setCongr hdomain rfl, fun x => ?_⟩
      obtain ⟨p, hpbase, hpval, hplo, hphi⟩ := hLp ⟨x, hdomain.symm ▸ x.property⟩
      exact ⟨p, hpbase, hpval, by simpa only [zero_add] using hplo, hphi⟩

end Homeomorph
