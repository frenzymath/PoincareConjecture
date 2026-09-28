import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarAngularCuts













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture.M64Uniformization

local notation "Cover" => ℝ × ℝ
local notation "Band" => Set.prod (Ioo (1 : ℝ) 2) (Ioo (0 : ℝ) 1)





theorem scalar_fractional_mem_band {z : Cover} (hz : z ∈ scalarCoverStrip)
    (hcut : z ∉ scalarAngularCuts) : z - (0, (⌊z.2⌋ : ℝ)) ∈ Band := by
  have hne : z.2 ≠ (⌊z.2⌋ : ℝ) := by
    intro heq
    exact hcut (mem_iUnion.mpr ⟨⌊z.2⌋, hz, heq⟩)
  exact ⟨by simpa [scalarCoverStrip] using hz, Int.fract_pos.mpr hne, Int.fract_lt_one _⟩





theorem scalar_injOn_off_cuts_of_fundamental_image {f : Cover → Cover}
    (hdeck : ∀ z ∈ scalarCoverStrip, ∀ n : ℤ,
      f (z - (0, (n : ℝ))) = f z - (0, (n : ℝ)))
    (hband : InjOn f Band)
    (hseparate : ∀ a ∈ f '' Band, ∀ k : ℤ, k ≠ 0 → a + (0, (k : ℝ)) ∉ f '' Band) :
    InjOn f (scalarCoverStrip \ scalarAngularCuts) := by
  intro x hx y hy hxy
  let n : ℤ := ⌊x.2⌋
  let m : ℤ := ⌊y.2⌋
  let u := x - (0, (n : ℝ))
  let v := y - (0, (m : ℝ))
  have hu : u ∈ Band := scalar_fractional_mem_band hx.1 hx.2
  have hv : v ∈ Band := scalar_fractional_mem_band hy.1 hy.2
  have hfu : f u = f x - (0, (n : ℝ)) := hdeck x hx.1 n
  have hfv : f v = f y - (0, (m : ℝ)) := hdeck y hy.1 m
  have hshift : f u + (0, ((n - m : ℤ) : ℝ)) = f v := by
    rw [hfu, hfv, hxy]
    ext <;> simp
  have hnm : n = m := by
    by_contra hne
    exact hseparate (f u) ⟨u, hu, rfl⟩ (n - m) (sub_ne_zero.mpr hne)
      (hshift ▸ show f v ∈ f '' Band from ⟨v, hv, rfl⟩)
  have huv : u = v := hband hu hv (by rw [hfu, hfv, hxy, hnm])
  have huveq : x - (0, (m : ℝ)) = y - (0, (m : ℝ)) := by
    simpa only [u, v, hnm] using huv
  exact sub_left_injective huveq





theorem scalar_injOn_strip_of_fundamental_image {f : Cover → Cover}
    (ho : ∀ z ∈ scalarCoverStrip, 𝓝 (f z) ≤ map f (𝓝 z))
    (hnull : volume (f '' scalarAngularCuts) = 0)
    (hdeck : ∀ z ∈ scalarCoverStrip, ∀ n : ℤ,
      f (z - (0, (n : ℝ))) = f z - (0, (n : ℝ)))
    (hband : InjOn f Band)
    (hseparate : ∀ a ∈ f '' Band, ∀ k : ℤ, k ≠ 0 → a + (0, (k : ℝ)) ∉ f '' Band) :
    InjOn f scalarCoverStrip := by
  have hoff := scalar_injOn_off_cuts_of_fundamental_image hdeck hband hseparate
  have himageOpen {S : Set Cover} (hS : IsOpen S) (hsub : S ⊆ scalarCoverStrip) :
      IsOpen (f '' S) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro _ ⟨z, hz, rfl⟩
    exact ho z (hsub hz) (Filter.image_mem_map (hS.mem_nhds hz))
  intro x hx y hy hfxy
  by_contra hxy
  obtain ⟨r, hr, hsmall⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem (scalarCoverStrip_isOpen.mem_nhds hx)
      (isOpen_compl_singleton.mem_nhds hxy))
  let A := Metric.ball x r
  let B := scalarCoverStrip \ Metric.closedBall x r
  have hAsub : A ⊆ scalarCoverStrip :=
    fun z hz => (hsmall (Metric.ball_subset_closedBall hz)).1
  have hyB : y ∈ B := ⟨hy, fun hyK => (hsmall hyK).2 rfl⟩
  have hAo : IsOpen A := Metric.isOpen_ball
  have hBo : IsOpen B := scalarCoverStrip_isOpen.sdiff Metric.isClosed_closedBall
  let W := (f '' A) ∩ (f '' B)
  have hWo : IsOpen W := (himageOpen hAo hAsub).inter (himageOpen hBo sdiff_subset)
  have hWne : W.Nonempty := ⟨f x, ⟨x, Metric.mem_ball_self hr, rfl⟩,
    ⟨y, hyB, hfxy.symm⟩⟩
  have hWpos : 0 < volume W := hWo.measure_pos volume hWne
  have hex : ∃ a ∈ W, a ∉ f '' scalarAngularCuts := by
    by_contra h
    push Not at h
    have hle : volume W ≤ volume (f '' scalarAngularCuts) := measure_mono h
    rw [hnull] at hle
    exact hWpos.not_ge hle
  obtain ⟨a, ⟨⟨u, hu, hfu⟩, ⟨v, hv, hfv⟩⟩, ha⟩ := hex
  have hucut : u ∉ scalarAngularCuts := fun h => ha ⟨u, h, hfu⟩
  have hvcut : v ∉ scalarAngularCuts := fun h => ha ⟨v, h, hfv⟩
  have huv : u = v := hoff ⟨hAsub hu, hucut⟩ ⟨hv.1, hvcut⟩ (hfu.trans hfv.symm)
  exact hv.2 (huv ▸ Metric.ball_subset_closedBall hu)

end PoincareConjecture.M64Uniformization
