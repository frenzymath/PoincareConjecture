import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceEdgeCommonOrientation
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicMinimizerSubsegments
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckAxialLength
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Intrinsic

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

open PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

private theorem neck_reversed_reversed (N : EpsilonNeck g) :
    N.reversed.reversed = N := by
  have hcoordinate : (RoundCylinderReflection.domain N.epsilon).trans
      ((RoundCylinderReflection.domain N.epsilon).trans N.coordinate) = N.coordinate := by
    apply Homeomorph.ext
    intro z
    change N.coordinate (RoundCylinderReflection.domain N.epsilon
      (RoundCylinderReflection.domain N.epsilon z)) = N.coordinate z
    congr 1
    change (z.1, (⟨-(-(z.2 : ℝ)),
      RoundCylinderReflection.neg_mem_interval
        (RoundCylinderReflection.neg_mem_interval z.2.property)⟩ :
          Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)) = z
    exact Prod.ext (by rfl) (Subtype.ext (neg_neg _))
  have hmap : (N.coordinate_map ∘ RoundCylinderReflection.space) ∘
      RoundCylinderReflection.space = N.coordinate_map := by
    funext z
    exact congrArg N.coordinate_map (RoundCylinderReflection.space_involutive z)
  have hinverse : RoundCylinderReflection.space ∘
      (RoundCylinderReflection.space ∘ N.coordinate_inverse) = N.coordinate_inverse := by
    funext x
    exact RoundCylinderReflection.space_involutive (N.coordinate_inverse x)
  cases N
  dsimp only at hcoordinate
  simp only [reversed, hmap, hinverse]
  congr 1

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]

private theorem frontier_old_orientations_opposite
    {N Pminus Pplus Nminus Qminus Nplus Qplus : EpsilonNeck g}
    {γ : ℝ → M} {a b u t v : ℝ}
    (Hplus : SourceEdgeCommonOrientationPacket Nplus Pplus Qplus (γ := γ) t v)
    (Hminus : SourceEdgeCommonOrientationPacket Nminus Pminus Qminus
      (γ := fun s => γ (-s)) (-t) (-u))
    (hplus : Nplus = N ∨ Nplus = N.reversed)
    (hminus : Nminus = N ∨ Nminus = N.reversed)
    (hε : N.epsilon ≤ 1 / 1000) {U : Set M} (hNU : N.carrier ⊆ U)
    (hau : a ≤ u) (htv : t < v) (hvb : v ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U)
    (hfinite : g.pathELength γ a b ≠ ⊤)
    (hmin : g.pathELength γ a b = intrinsicEDist g U (γ a) (γ b)) :
    Nminus = Nplus.reversed := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hplusε : Nplus.epsilon = N.epsilon := by
    rcases hplus with h | h <;> simp only [h, reversed_epsilon]
  have hplusU : Nplus.carrier ⊆ U := by
    rcases hplus with h | h <;> simpa only [h, reversed_carrier] using hNU
  have hApos : 0 < Nplus.epsilon⁻¹ := inv_pos.mpr Nplus.epsilon_pos
  have hA : (1000 : ℝ) ≤ Nplus.epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right (hplusε.trans_le hε) hApos.le
    rw [mul_inv_cancel₀ Nplus.epsilon_pos.ne'] at h
    linarith only [h]
  have hbad (hequal : Nminus = Nplus) : False := by
    obtain ⟨d, hd, hdlevel, _, _⟩ := Hplus.transition
    obtain ⟨e, he, helevel, _, _⟩ := Hminus.transition
    have huc : u < -e := by linarith only [he.2]
    have hct : -e < t := by linarith only [he.1]
    have hcd : -e < d := hct.trans hd.1
    have hclevel : (Nplus.coordinate_inverse (γ (-e))).2 =
        (509 : ℝ) * Nplus.epsilon⁻¹ / 512 := by
      change (Nminus.coordinate_inverse (γ (-e))).2 =
        (509 : ℝ) * Nminus.epsilon⁻¹ / 512 at helevel
      simpa only [hequal] using helevel
    have hcdN : MapsTo γ (Icc (-e) d) Nplus.carrier := by
      intro s hs
      by_cases hst : s ≤ t
      · have hs' : -s ∈ Ico (-t) (-u) :=
          ⟨neg_le_neg hst, by linarith only [hs.1, huc]⟩
        have h := Hminus.edge hs'
        simpa only [hequal, neg_neg] using h
      · exact Hplus.edge ⟨(lt_of_not_ge hst).le, hs.2.trans_lt hd.2⟩
    have hcN : γ (-e) ∈ Nplus.carrier := hcdN (left_mem_Icc.mpr hcd.le)
    have hdN : γ d ∈ Nplus.carrier := hcdN (right_mem_Icc.mpr hcd.le)
    have hminimum := pathELength_eq_intrinsicEDist_subsegment g
      (hau.trans huc.le) hcd.le (hd.2.le.trans hvb) hγ hγU hfinite hmin
    have hupper := (intrinsicEDist_mono_of_subset (g := g) hplusU).trans
      (Nplus.intrinsicEDist_le_axial_add hcN hdN)
    rw [hdlevel, hclevel, sub_self, abs_zero, zero_add] at hupper
    have hroot : Real.sqrt (1 + Nplus.epsilon) ≤ (2 : ℝ) := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨by norm_num, by linarith only [Nplus.epsilon_lt_half]⟩
    have hsqrt2 : Real.sqrt 2 ≤ (2 : ℝ) :=
      (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
    have hsphere : Real.sqrt 2 * (Real.pi + 1) ≤ (10 : ℝ) := by
      calc
        _ ≤ 2 * (Real.pi + 1) :=
          mul_le_mul_of_nonneg_right hsqrt2 (by positivity)
        _ ≤ 10 := by linarith only [Real.pi_le_four]
    have hcoefficient : Real.sqrt (1 + Nplus.epsilon) *
        (Real.sqrt 2 * (Real.pi + 1)) ≤ (20 : ℝ) := by
      have h := mul_le_mul hroot hsphere
        (by positivity : 0 ≤ Real.sqrt 2 * (Real.pi + 1)) (by norm_num)
      norm_num at h
      exact h
    have hscaled : Nplus.scale * Real.sqrt (1 + Nplus.epsilon) *
        (Real.sqrt 2 * (Real.pi + 1)) ≤ 20 * Nplus.scale := by
      have h := mul_le_mul_of_nonneg_left hcoefficient Nplus.scale_pos.le
      nlinarith only [h]
    have hshort : intrinsicEDist g U (γ (-e)) (γ d) ≤
        ENNReal.ofReal (20 * Nplus.scale) :=
      hupper.trans (ENNReal.ofReal_le_ofReal hscaled)
    have htzero : (Nplus.coordinate_inverse (γ t)).2 = 0 := by
      rw [Hplus.center_N]
      exact (Nplus.mem_central_sphere_iff_of_mem_carrier
        (Nplus.central_sphere_subset Nplus.center_on_central_sphere)).mp
          Nplus.center_on_central_sphere
    have hcost := path_axial_displacement_le Nplus hct.le
      (hγ.mono (Icc_subset_Icc (hau.trans huc.le) (htv.le.trans hvb)))
      (fun s hs => hcdN ⟨hs.1, hs.2.trans hd.1.le⟩)
    rw [htzero, zero_sub, abs_neg, hclevel,
      abs_of_pos (by positivity : 0 < (509 : ℝ) * Nplus.epsilon⁻¹ / 512)] at hcost
    have hlong : ENNReal.ofReal ((Nplus.scale / 2) *
        ((509 : ℝ) * Nplus.epsilon⁻¹ / 512)) ≤ g.pathELength γ (-e) d :=
      hcost.trans (Manifold.pathELength_mono le_rfl hd.1.le)
    rw [hminimum] at hlong
    have hgap : 20 * Nplus.scale < (Nplus.scale / 2) *
        ((509 : ℝ) * Nplus.epsilon⁻¹ / 512) := by
      have h : (20 : ℝ) < (1 / 2 : ℝ) *
          ((509 : ℝ) * Nplus.epsilon⁻¹ / 512) := by linarith only [hA]
      have hs := mul_lt_mul_of_pos_left h Nplus.scale_pos
      nlinarith only [hs]
    have hpositive : 0 < (Nplus.scale / 2) *
        ((509 : ℝ) * Nplus.epsilon⁻¹ / 512) := by
      have := Nplus.scale_pos
      have := inv_pos.mpr Nplus.epsilon_pos
      positivity
    exact (not_lt_of_ge (hlong.trans hshort))
      ((ENNReal.ofReal_lt_ofReal_iff hpositive).mpr hgap)
  rcases hplus with hp | hp <;> rcases hminus with hm | hm
  · exact False.elim (hbad (hm.trans hp.symm))
  · rw [hm, hp]
  · rw [hm, hp, neck_reversed_reversed]
  · exact False.elim (hbad (hm.trans hp.symm))

theorem exists_neck_frontier_orientation_pair_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
      ∀ (N Pminus Pplus : EpsilonNeck g), N.epsilon ≤ epsilon₀ →
        Pminus.epsilon = N.epsilon → Pplus.epsilon = N.epsilon →
      ∀ {U : Set M}, N.carrier ⊆ U →
      ∀ {γ : ℝ → M} {a b u t v : ℝ}, a ≤ u → u < t → t < v → v ≤ b →
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b) → MapsTo γ (Icc a b) U →
        g.pathELength γ a b ≠ ⊤ →
        g.pathELength γ a b = intrinsicEDist g U (γ a) (γ b) →
        γ t = N.center → γ u = Pminus.center → γ v = Pplus.center →
        MapsTo γ (Ioc u t) N.carrier → MapsTo γ (Ico t v) N.carrier →
        Pminus.center ∈ frontier N.carrier → Pplus.center ∈ frontier N.carrier →
        ∃ Nplus Qplus Nminus Qminus : EpsilonNeck g,
          (Nplus = N ∨ Nplus = N.reversed) ∧
          (Nminus = N ∨ Nminus = N.reversed) ∧
          SourceEdgeCommonOrientationPacket Nplus Pplus Qplus (γ := γ) t v ∧
          SourceEdgeCommonOrientationPacket Nminus Pminus Qminus
            (γ := fun s => γ (-s)) (-t) (-u) ∧ Nminus = Nplus.reversed := by
  obtain ⟨epsilon₀, hpos, hsmall, hpacket⟩ :=
    exists_source_edge_common_orientation_packet.{u}
  have hsmall' : epsilon₀ ≤ (1 / 1000 : ℝ) := hsmall.trans (by norm_num)
  refine ⟨epsilon₀, hpos, hsmall', ?_⟩
  intro M _ _ _ _ _ _ _ g N Pminus Pplus hε hminusε hplusε U hNU
    γ a b u t v hau hut htv hvb hγ hγU hfinite hmin hc hcm hcp
    hleft hright hfrontminus hfrontplus
  obtain ⟨Nplus, Qplus, hplus, Hplus⟩ := hpacket N Pplus hε hplusε htv
    (hγ.mono (Icc_subset_Icc (hau.trans hut.le) hvb)) hc hcp hright hfrontplus
  let η : ℝ → M := fun s => γ (-s)
  have hneg : MapsTo (fun s : ℝ => -s) (Icc (-t) (-u)) (Icc a b) := by
    intro s hs
    constructor <;> linarith only [hs.1, hs.2, hau, htv, hvb]
  have hη : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 η (Icc (-t) (-u)) :=
    hγ.comp (show ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (fun s : ℝ => -s) from
      contMDiff_id.neg).contMDiffOn hneg
  have hηcenter : η (-t) = N.center := by simpa only [η, neg_neg] using hc
  have hηminus : η (-u) = Pminus.center := by simpa only [η, neg_neg] using hcm
  have hηedge : MapsTo η (Ico (-t) (-u)) N.carrier := by
    intro s hs
    have hs' : -s ∈ Ioc u t := by
      constructor <;> linarith only [hs.1, hs.2]
    exact hleft hs'
  obtain ⟨Nminus, Qminus, hminus, Hminus⟩ := hpacket N Pminus hε hminusε
    (neg_lt_neg hut) hη hηcenter hηminus hηedge hfrontminus
  refine ⟨Nplus, Qplus, Nminus, Qminus, hplus, hminus, Hplus, Hminus, ?_⟩
  exact frontier_old_orientations_opposite Hplus Hminus hplus hminus
    (hε.trans hsmall') hNU hau htv hvb hγ hγU hfinite hmin

end PoincareConjecture.M28
