import PoincareConjecture.Proofs.M25.AppA_1_Necks.SaturatedHeight
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.SmoothTransition












set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck




theorem isSeparating_of_central_sphere_graph
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (N N' : EpsilonNeck g) (hsep : N.IsSeparating)
    (f : UnitTwoSphere → ℝ) (hf : Continuous f)
    (hdom : ∀ q, f q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hgraph : N'.central_sphere =
      range (fun q : UnitTwoSphere => N.coordinate_map (q, f q))) :
    N'.IsSeparating := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let L := N.epsilon⁻¹
  have hL : 0 < L := inv_pos.mpr N.epsilon_pos
  let q0 := (N.coordinate_inverse N.center).1
  obtain ⟨qm, _, hmax⟩ :=
    (isCompact_univ : IsCompact (univ : Set UnitTwoSphere)).exists_isMaxOn
      ⟨q0, mem_univ _⟩ hf.abs.continuousOn
  let a := max |f qm| (L / 4)
  let b := (a + L) / 2
  have ha : 0 < a := (by dsimp only [a]; exact lt_max_of_lt_right (by positivity))
  have haL : a < L := by
    apply max_lt (abs_lt.mpr (hdom qm))
    linarith
  have hab : a < b := by dsimp only [b]; linarith
  have hb : 0 < b := ha.trans hab
  have hbL : b < L := by dsimp only [b]; linarith
  have hfbound (q : UnitTwoSphere) : |f q| ≤ a :=
    (hmax (mem_univ q)).trans (le_max_left _ _)
  let chi : ℝ → ℝ := fun s => Real.smoothTransition ((b - |s|) / (b - a))
  have hchi : Continuous chi :=
    Real.smoothTransition.continuous.comp
      ((continuous_const.sub continuous_abs).div_const (b - a))
  have hchibounds (s : ℝ) : 0 ≤ chi s ∧ chi s ≤ 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hchione {s : ℝ} (hs : |s| ≤ a) : chi s = 1 := by
    apply Real.smoothTransition.one_of_one_le
    exact (le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)
  have hchizero {s : ℝ} (hs : b ≤ |s|) : chi s = 0 :=
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_pos.mpr hab).le)
  let K := N.coordinate_map '' (univ ×ˢ Icc (-b) b)
  have hK : IsCompact K := N.isCompact_coordinate_slab (by change -L < -b; linarith) hbL
  have hKU : K ⊆ N.carrier := by
    rintro x ⟨z, hz, rfl⟩
    exact N.coordinate_map_mem ⟨mem_univ _,
      (neg_lt_neg hbL).trans_le hz.2.1, hz.2.2.trans_lt hbL⟩
  have hmemK {x : M} (hx : x ∈ N.carrier)
      (hs : |(N.coordinate_inverse x).2| ≤ b) : x ∈ K :=
    ⟨N.coordinate_inverse x, ⟨mem_univ _, abs_le.mp hs⟩, N.coordinate_map_inverse hx⟩
  let G : M → ℝ := fun x => if x ∈ N.carrier then
    chi (N.coordinate_inverse x).2 * f (N.coordinate_inverse x).1 else 0
  have hGzero {x : M} (hx : x ∉ K) : G x = 0 := by
    by_cases hxU : x ∈ N.carrier
    · have hs : b ≤ |(N.coordinate_inverse x).2| := by
        exact (lt_of_not_ge (fun h => hx (hmemK hxU h))).le
      simp only [G, if_pos hxU, hchizero hs, zero_mul]
    · simp only [G, if_neg hxU]
  have hG : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ N.carrier
    · have hc := N.coordinate_inverse_smooth.continuousOn.continuousAt
        (N.carrier_open.mem_nhds hx)
      apply ((hchi.continuousAt.comp hc.snd).mul
        (hf.continuousAt.comp hc.fst)).congr_of_eventuallyEq
      filter_upwards [N.carrier_open.mem_nhds hx] with y hy
      simp only [G, if_pos hy]
      rfl
    · have hxK : x ∉ K := fun h => hx (hKU h)
      apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
      exact hGzero hy
  obtain ⟨xminus, xplus, hxminus, hxplus, _, _, _, _, _, hcover⟩ :=
    N.exists_opposite_central_components hsep
  obtain ⟨H, hH, hinside, hminus, hplus, _, _⟩ :=
    N.exists_saturatedAxialHeight hsep xminus xplus hxminus hxplus
  let F : M → ℝ := fun x => H x - G x
  have hF : Continuous F := hH.sub hG
  have hGraphU : N'.central_sphere ⊆ N.carrier := by
    rw [hgraph]
    rintro x ⟨q, rfl⟩
    exact N.coordinate_map_mem ⟨mem_univ _, hdom q⟩
  have hzero {x : M} (hx : x ∈ connectedComponent N.center) :
      F x = 0 ↔ x ∈ N'.central_sphere := by
    by_cases hxU : x ∈ N.carrier
    · have hFx : F x = (N.coordinate_inverse x).2 -
          chi (N.coordinate_inverse x).2 * f (N.coordinate_inverse x).1 := by
        simp only [F, G, if_pos hxU, hinside x hxU]
      rw [hFx, sub_eq_zero, hgraph]
      constructor
      · intro hs
        have hsbound : |(N.coordinate_inverse x).2| ≤ a := by
          calc
            _ = |chi (N.coordinate_inverse x).2| * |f (N.coordinate_inverse x).1| := by
              conv_lhs => rw [hs]
              exact abs_mul _ _
            _ ≤ |f (N.coordinate_inverse x).1| := by
              rw [abs_of_nonneg (hchibounds _).1]
              nlinarith [(hchibounds (N.coordinate_inverse x).2).2,
                abs_nonneg (f (N.coordinate_inverse x).1)]
            _ ≤ a := hfbound _
        rw [hchione hsbound, one_mul] at hs
        refine ⟨(N.coordinate_inverse x).1, ?_⟩
        change N.coordinate_map ((N.coordinate_inverse x).1,
          f (N.coordinate_inverse x).1) = x
        rw [← hs]
        exact N.coordinate_map_inverse hxU
      · rintro ⟨q, rfl⟩
        rw [N.coordinate_inverse_map (q, f q) (hdom q), hchione (hfbound q), one_mul]
    · have hGx : G x = 0 := by simp only [G, if_neg hxU]
      have hHx : H x = -L ∨ H x = L := by
        rw [← hcover] at hx
        rcases hx with (hxA | hxS) | hxB
        · exact Or.inl (hminus x ⟨hxA, hxU⟩)
        · exact False.elim (hxU (N.central_sphere_subset hxS))
        · exact Or.inr (hplus x ⟨hxB, hxU⟩)
      have hFn : F x ≠ 0 := by
        dsimp only [F]
        rw [hGx, sub_zero]
        rcases hHx with h | h <;> rw [h] <;> linarith
      exact iff_of_false hFn (fun hs => hxU (hGraphU hs))
  have hcomponent : connectedComponent N'.center = connectedComponent N.center :=
    (connectedComponent_eq
      (N.m25_carrier_subset_connectedComponent (hGraphU N'.center_on_central_sphere))).symm
  have hpoints (s : ℝ) (hs : s ∈ Ioo (-L) L) (hsb : b ≤ |s|) :
      N.coordinate_map (q0, s) ∈ connectedComponent N.center ∧
        F (N.coordinate_map (q0, s)) = s := by
    have hx : N.coordinate_map (q0, s) ∈ N.carrier :=
      N.coordinate_map_mem ⟨mem_univ _, hs⟩
    refine ⟨N.m25_carrier_subset_connectedComponent hx, ?_⟩
    simp only [F, G, if_pos hx, hinside _ hx,
      N.coordinate_inverse_map (q0, s) hs, hchizero hsb, zero_mul, sub_zero]
  have hpos := hpoints b ⟨by linarith, hbL⟩ (by rw [abs_of_pos hb])
  have hneg := hpoints (-b) ⟨by linarith, by linarith⟩ (by rw [abs_neg, abs_of_pos hb])
  have hposmem : N.coordinate_map (q0, b) ∈
      connectedComponent N.center \ N'.central_sphere := by
    refine ⟨hpos.1, ?_⟩
    intro h
    have hz := (hzero hpos.1).mpr h
    rw [hpos.2] at hz
    exact hb.ne' hz
  have hnegmem : N.coordinate_map (q0, -b) ∈
      connectedComponent N.center \ N'.central_sphere := by
    refine ⟨hneg.1, ?_⟩
    intro h
    have hz := (hzero hneg.1).mpr h
    rw [hneg.2] at hz
    linarith
  change (connectedComponent N'.center \ N'.central_sphere).Nonempty ∧
    ¬ IsConnected (connectedComponent N'.center \ N'.central_sphere)
  rw [hcomponent]
  refine ⟨⟨_, hposmem⟩, ?_⟩
  intro hconn
  have hne : ∀ x ∈ connectedComponent N.center \ N'.central_sphere, F x ≠ 0 :=
    fun x hx hz => hx.2 ((hzero hx.1).mp hz)
  have hp : 0 < F (N.coordinate_map (q0, b)) := by rw [hpos.2]; exact hb
  have hn := hconn.isPreconnected.lt_of_ne hF.continuousOn hne
    ⟨_, hposmem, hp⟩ hnegmem
  rw [hneg.2] at hn
  linarith

end PoincareConjecture.EpsilonNeck
