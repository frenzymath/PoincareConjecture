import PoincareConjecture.Proofs.M76.Mathlib.CertifiedDirectionalIsotopy
import PoincareConjecture.Proofs.M76.Mathlib.GeometricBandLevelCharts
import PoincareConjecture.Proofs.M76.Mathlib.PointedDiskHeight
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLLevelImages

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePL.exists_pointed_cap_collar_isotopy_with_rim_intervals_global_finitePL_and_signs
    {B T d b U : Set E} {upper : E → ℝ} (hupper : ∀ x ∈ B, 0 ≤ upper x)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (hdplane : d ⊆ {x | A x = 0})
    (q : b) (hcap : d ∩ T = b) (v : E) (hv : A.linear v = 1)
    (Q : SimplicialComplex ℝ E) (hQ : Q.faces.Finite)
    (hQd : d ∩ Q.space ⊆ {(q : E)}) (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ f : E × ℝ → E, (∀ p, (C p : E) = f p) ∧
      ∃ r : E → ℝ, FinitePiecewiseAffineOn r d ∧
        (∀ x ∈ d, r x ∈ Icc 0 2 ∧ (r x = 0 ↔ x = q)) ∧
        (∃ p ∈ b, r p = 2 ∧ ∀ x ∈ d, r x = 2 ↔ x = p) ∧
        (∀ x ∈ d,
          (0 < r x → x ∈ closure (d ∩ {y | r y < r x})) ∧
            (r x < 2 → x ∈ closure (d ∩ {y | r x < r y}))) ∧
        (∀ a : ℝ, a ∈ Ioo 0 2 →
          IsFinitePLBallPair ℝ (b ∩ {x | r x ≤ a}) (b ∩ {x | r x = a})) ∧
        (∀ a : ℝ, a ∈ Ioo 0 2 →
          IsFinitePLBallPair ℝ (b ∩ {x | a ≤ r x}) (b ∩ {x | r x = a})) ∧
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
              IsFinitePLBallPair (ℝ × ℝ) (H t '' d) (H t '' b) ∧
              ((t : ℝ) ≠ 0 → ∀ a : ℝ, a ∈ Ioo 0 2 →
                IsFinitePLBallPair ℝ ((H t '' d) ∩ {x | A x = (t : ℝ) * a})
                  ((H t '' b) ∩ {x | A x = (t : ℝ) * a})) ∧
              (∀ c : ℝ, ((H t '' d) ∩ {x | A x = c}) ∩
                  ((H t '' T) ∩ {x | A x = c}) = (H t '' b) ∩ {x | A x = c}) ∧
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
  obtain ⟨r, hr, hmin, hmax, hsigns, hrlevels, hrsub, hrsuper⟩ :=
    hd.exists_pointed_height_with_rim_intervals_and_signs q
  obtain ⟨g, hgn, hgr, hgQ, hgU, ε₀, hε₀, H₀, hc₀, hci₀, hformula,
      R, hR, _, hcover, hgR, _, hPL, hglobal⟩ :=
    hr.exists_certified_directional_isotopy_with_global_finitePL (fun x hx => (hmin x hx).1.1)
      A v hv Q hQ (fun x hx => (hmin x hx.1).2.mpr (hQd hx)) hU hdU hTc
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
  refine ⟨f, hfval, r, hr, hmin, hmax, hsigns, hrsub, hrsuper, g, hgT, hgn, hgr, hgQ, hgU,
    ε, hε, H, (fun t => hglobal (embed t)), ?_, ?_, hHval, fun t => ?_⟩
  · exact hc₀.comp ((hembed.comp continuous_fst).prodMk continuous_snd)
  · exact hci₀.comp ((hembed.comp continuous_fst).prodMk continuous_snd)
  · have hHd : FinitePiecewiseAffineOn (H t : E → E) d := by
      rw [← hJds]
      exact (hPL (embed t)).restrict Jd hJd (hJds.subset.trans hdR)
    have hHT : FinitePiecewiseAffineOn (H t : E → E) T := by
      rw [← hJTs]
      exact (hPL (embed t)).restrict JT hJT (hJTs.subset.trans hTR)
    have hcapheight (x : E) (hx : x ∈ d) : A (H t x) = (t : ℝ) * r x := by
      rw [hHval, hgr hx, add_comm x]
      change A (((t : ℝ) * r x) • v +ᵥ x) = (t : ℝ) * r x
      rw [A.map_vadd, map_smul, hv]
      change (t : ℝ) * r x * 1 + A x = (t : ℝ) * r x
      rw [hdplane hx, mul_one, add_zero]
    refine ⟨hHd, hHT, hd.image hHd (H t).injective.injOn, ?_, ?_, ?_⟩
    · intro ht a ha
      exact hHd.image_level_ballPair (H t).injective.injOn Subset.rfl hd.1 ht
        hcapheight (hrlevels a ha)
    · intro c
      have hinter : (H t '' d) ∩ (H t '' T) = H t '' b := by
        rw [← image_inter (H t).injective, hcap]
      ext x
      have hx := Set.ext_iff.mp hinter x
      simp only [mem_inter_iff] at *
      tauto
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

theorem IsFinitePL.exists_pointed_cap_collar_isotopy_with_rim_intervals_with_global_finitePL
    {B T d b U : Set E} {upper : E → ℝ} (hupper : ∀ x ∈ B, 0 ≤ upper x)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (hdplane : d ⊆ {x | A x = 0})
    (q : b) (hcap : d ∩ T = b) (v : E) (hv : A.linear v = 1)
    (Q : SimplicialComplex ℝ E) (hQ : Q.faces.Finite)
    (hQd : d ∩ Q.space ⊆ {(q : E)}) (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ f : E × ℝ → E, (∀ p, (C p : E) = f p) ∧
      ∃ r : E → ℝ, FinitePiecewiseAffineOn r d ∧
        (∀ x ∈ d, r x ∈ Icc 0 2 ∧ (r x = 0 ↔ x = q)) ∧
        (∃ p ∈ b, r p = 2 ∧ ∀ x ∈ d, r x = 2 ↔ x = p) ∧
        (∀ a : ℝ, a ∈ Ioo 0 2 →
          IsFinitePLBallPair ℝ (b ∩ {x | r x ≤ a}) (b ∩ {x | r x = a})) ∧
        (∀ a : ℝ, a ∈ Ioo 0 2 →
          IsFinitePLBallPair ℝ (b ∩ {x | a ≤ r x}) (b ∩ {x | r x = a})) ∧
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
              IsFinitePLBallPair (ℝ × ℝ) (H t '' d) (H t '' b) ∧
              ((t : ℝ) ≠ 0 → ∀ a : ℝ, a ∈ Ioo 0 2 →
                IsFinitePLBallPair ℝ ((H t '' d) ∩ {x | A x = (t : ℝ) * a})
                  ((H t '' b) ∩ {x | A x = (t : ℝ) * a})) ∧
              (∀ c : ℝ, ((H t '' d) ∩ {x | A x = c}) ∩
                  ((H t '' T) ∩ {x | A x = c}) = (H t '' b) ∩ {x | A x = c}) ∧
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
  obtain ⟨f, hfval, r, hr, hmin, hmax, _, hrest⟩ :=
    hC.exists_pointed_cap_collar_isotopy_with_rim_intervals_global_finitePL_and_signs
      hupper A hheight hd hdplane q hcap v hv Q hQ hQd hU hdU
  exact ⟨f, hfval, r, hr, hmin, hmax, hrest⟩

theorem IsFinitePL.exists_pointed_cap_collar_isotopy_with_rim_intervals
    {B T d b U : Set E} {upper : E → ℝ} (hupper : ∀ x ∈ B, 0 ≤ upper x)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (hdplane : d ⊆ {x | A x = 0})
    (q : b) (hcap : d ∩ T = b) (v : E) (hv : A.linear v = 1)
    (Q : SimplicialComplex ℝ E) (hQ : Q.faces.Finite)
    (hQd : d ∩ Q.space ⊆ {(q : E)}) (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ f : E × ℝ → E, (∀ p, (C p : E) = f p) ∧
      ∃ r : E → ℝ, FinitePiecewiseAffineOn r d ∧
        (∀ x ∈ d, r x ∈ Icc 0 2 ∧ (r x = 0 ↔ x = q)) ∧
        (∃ p ∈ b, r p = 2 ∧ ∀ x ∈ d, r x = 2 ↔ x = p) ∧
        (∀ a : ℝ, a ∈ Ioo 0 2 →
          IsFinitePLBallPair ℝ (b ∩ {x | r x ≤ a}) (b ∩ {x | r x = a})) ∧
        (∀ a : ℝ, a ∈ Ioo 0 2 →
          IsFinitePLBallPair ℝ (b ∩ {x | a ≤ r x}) (b ∩ {x | r x = a})) ∧
        ∃ g : E → ℝ, FinitePiecewiseAffineOn g T ∧ (∀ x, 0 ≤ g x) ∧
          EqOn g r d ∧ (∀ x ∈ Q.space, g x = 0) ∧ (∀ x, x ∉ U → g x = 0) ∧
          ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
            Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
            Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
            (∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v) ∧
            ∀ t : Icc (-ε) ε,
              FinitePiecewiseAffineOn (H t : E → E) d ∧
              FinitePiecewiseAffineOn (H t : E → E) T ∧
              IsFinitePLBallPair (ℝ × ℝ) (H t '' d) (H t '' b) ∧
              ((t : ℝ) ≠ 0 → ∀ a : ℝ, a ∈ Ioo 0 2 →
                IsFinitePLBallPair ℝ ((H t '' d) ∩ {x | A x = (t : ℝ) * a})
                  ((H t '' b) ∩ {x | A x = (t : ℝ) * a})) ∧
              (∀ c : ℝ, ((H t '' d) ∩ {x | A x = c}) ∩
                  ((H t '' T) ∩ {x | A x = c}) = (H t '' b) ∩ {x | A x = c}) ∧
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
  obtain ⟨f, hf, r, hr, hmin, hmax, hrsub, hrsuper, g, hgT, hgn, hgr, hgQ, hgU,
      ε, hε, H, _, hrest⟩ :=
    hC.exists_pointed_cap_collar_isotopy_with_rim_intervals_with_global_finitePL
      hupper A hheight hd hdplane q hcap v hv Q hQ hQd hU hdU
  exact ⟨f, hf, r, hr, hmin, hmax, hrsub, hrsuper, g, hgT, hgn, hgr, hgQ, hgU,
    ε, hε, H, hrest⟩

theorem IsFinitePL.exists_pointed_cap_collar_isotopy
    {B T d b U : Set E} {upper : E → ℝ} (hupper : ∀ x ∈ B, 0 ≤ upper x)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (hdplane : d ⊆ {x | A x = 0})
    (q : b) (hcap : d ∩ T = b) (v : E) (hv : A.linear v = 1)
    (Q : SimplicialComplex ℝ E) (hQ : Q.faces.Finite)
    (hQd : d ∩ Q.space ⊆ {(q : E)}) (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ f : E × ℝ → E, (∀ p, (C p : E) = f p) ∧
      ∃ r : E → ℝ, FinitePiecewiseAffineOn r d ∧
        (∀ x ∈ d, r x ∈ Icc 0 2 ∧ (r x = 0 ↔ x = q)) ∧
        (∀ a : ℝ, a ∈ Ioo 0 2 →
          IsFinitePLBallPair ℝ (b ∩ {x | r x ≤ a}) (b ∩ {x | r x = a})) ∧
        ∃ g : E → ℝ, FinitePiecewiseAffineOn g T ∧ (∀ x, 0 ≤ g x) ∧
          EqOn g r d ∧ (∀ x ∈ Q.space, g x = 0) ∧ (∀ x, x ∉ U → g x = 0) ∧
          ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
            Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
            Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
            (∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v) ∧
            ∀ t : Icc (-ε) ε,
              FinitePiecewiseAffineOn (H t : E → E) d ∧
              FinitePiecewiseAffineOn (H t : E → E) T ∧
              IsFinitePLBallPair (ℝ × ℝ) (H t '' d) (H t '' b) ∧
              ((t : ℝ) ≠ 0 → ∀ a : ℝ, a ∈ Ioo 0 2 →
                IsFinitePLBallPair ℝ ((H t '' d) ∩ {x | A x = (t : ℝ) * a})
                  ((H t '' b) ∩ {x | A x = (t : ℝ) * a})) ∧
              (∀ c : ℝ, ((H t '' d) ∩ {x | A x = c}) ∩
                  ((H t '' T) ∩ {x | A x = c}) = (H t '' b) ∩ {x | A x = c}) ∧
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
  obtain ⟨f, hf, r, hr, hmin, _, hrsub, _, hrest⟩ :=
    hC.exists_pointed_cap_collar_isotopy_with_rim_intervals hupper A hheight hd hdplane
      q hcap v hv Q hQ hQd hU hdU
  exact ⟨f, hf, r, hr, hmin, hrsub, hrest⟩

end Homeomorph
