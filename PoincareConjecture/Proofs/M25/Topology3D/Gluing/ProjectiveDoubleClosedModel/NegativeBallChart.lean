import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ProjectiveDoubleClosedModel.NegativeData
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.BallDiffeomorphism
import Mathlib.Topology.Order.IntermediateValue










set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M} {C1 C2 : ClosedModelCapData g}
  {P2 : PoincareConjecture.StandardPuncturedProjectiveCover M C2.puncture C2.carrier}




theorem NegativeProjectiveSideData.exists_ball_chart
    (d : NegativeProjectiveSideData C1 C2 P2) :
    let L := C1.epsilon⁻¹
    let c := (d.v + L) / 2
    let h := (L - d.v) / 4
    let a := c - h * (3 / 4)
    let b := c - h * (1 / 2)
    let W := fun s => (C1.carrier ∪ C2.carrier) \
      (C1.carrier \ C1.region s L)
    ∃ J2 : OpenPartialHomeomorph M E3,
      J2.source = W a ∧ J2.target = ball 0 (d.S.radial (3 / 4)) ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ J2 J2.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ J2.symm J2.target ∧
      (J2.symm : E3 → M) = P2.cover ∘ d.e ∧
      (∀ (q : UnitTwoSphere) (t : ℝ), t ∈ Icc (1 / 2) (3 / 4) →
        J2.symm (d.S.radial t • (d.S.boundary_map q).val) =
          C1.coordinate_map (q, c - h * t) ∧
        J2 (C1.coordinate_map (q, c - h * t)) =
          d.S.radial t • (d.S.boundary_map q).val) ∧
      J2 '' C1.region a b =
        {z : E3 | d.S.radial (1 / 2) < ‖z‖ ∧ ‖z‖ < d.S.radial (3 / 4)} := by
  classical
  let L := C1.epsilon⁻¹
  let N := C1
  let Y := C1.carrier ∪ C2.carrier
  let K (s : ℝ) := C1.carrier \ N.region s L
  let V (s : ℝ) := interior (K s)
  let W (s : ℝ) := Y \ K s
  let Q (s : ℝ) := Y \ V s
  let c := (d.v + L) / 2
  let h := (L - d.v) / 4
  let a := c - h * (3 / 4)
  let b := c - h * (1 / 2)
  let D (t : ℝ) := d.e '' closedBall 0 (d.S.radial t)
  let f : E3 → M := P2.cover ∘ d.e
  have hh : 0 < h := by dsimp [h, L]; linarith [d.v_mem.2]
  have hleft : d.v < c - h := by dsimp [c, h, L]; linarith [d.v_mem.2]
  have hright : c + h < L := by dsimp [c, h, L]; linarith [d.v_mem.2]
  have hva : d.v < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a, b]; linarith
  have hbL : b < L := by dsimp [b]; linarith
  have hheight {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) (13 / 16)) :
      c - h * t ∈ Ioo d.v L := by
    constructor <;> nlinarith [ht.1, ht.2]
  have hlarge {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) (13 / 16)) :
      t ∈ Icc (1 / 4 : ℝ) (7 / 8) := by
    constructor <;> linarith [ht.1, ht.2]
  have hneg := d.negative
  change ∀ t ∈ Icc (1 / 2 : ℝ) (13 / 16),
    projectiveCoverDomain C2.puncture ∩ P2.cover ⁻¹' Q (c + h * (d.S.side * t)) =
        D t ∪ (fun x : UnitThreeSphere => -x) '' D t ∧
    projectiveCoverDomain C2.puncture ∩ P2.cover ⁻¹' W (c + h * (d.S.side * t)) =
        interior (D t) ∪ (fun x : UnitThreeSphere => -x) '' interior (D t) at hneg
  simp only [d.side_eq, neg_one_mul, mul_neg, ← sub_eq_add_neg] at hneg
  have hvalid {x : E3} (hx : x ∈ ball 0 (d.S.radial (13 / 16))) :
      d.e x ∈ projectiveCoverDomain C2.puncture := by
    have hxD : d.e x ∈ D (13 / 16) := ⟨x, ball_subset_closedBall hx, rfl⟩
    have hm : d.e x ∈ projectiveCoverDomain C2.puncture ∩
        P2.cover ⁻¹' Q (c - h * (13 / 16)) := by
      rw [(hneg (13 / 16) (by norm_num)).1]
      exact Or.inl hxD
    exact hm.1
  have hstarR : d.S.radial (13 / 16) < d.S.radial (7 / 8) :=
    d.S.radial_strictMono (by norm_num) (by norm_num) (by norm_num)
  have h0star : d.S.radial (3 / 4) < d.S.radial (13 / 16) :=
    d.S.radial_strictMono (by norm_num) (by norm_num) (by norm_num)
  have hes {x : E3} (hx : x ∈ ball 0 (d.S.radial (13 / 16))) : x ∈ d.e.source := by
    rw [d.source_eq]
    exact ball_subset_ball hstarR.le hx
  have hinj : InjOn f (ball 0 (d.S.radial (13 / 16))) := by
    intro x hx y hy hxy
    rcases (P2.fibers (d.e x) (d.e y) (hvalid hx) (hvalid hy)).mp hxy with he | he
    · exact d.e.injOn (hes hx) (hes hy) he
    · exact False.elim ((disjoint_left.mp d.disjoint) (d.e.map_source (hes hx))
        ⟨d.e y, d.e.map_source (hes hy), he.symm⟩)
  let de : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 UnitThreeSphere ∞ :=
    { toPartialEquiv := d.e.toPartialEquiv
      open_source := d.e.open_source
      open_target := d.e.open_target
      contMDiffOn_toFun := d.smooth
      contMDiffOn_invFun := d.inverse_smooth }
  have hlocal : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ f
      (ball 0 (d.S.radial (13 / 16))) := by
    intro x
    have he : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ d.e x :=
      ⟨de, hes x.property, fun _ _ => rfl⟩
    exact he.comp (𝓡 3) M (P2.local_diffeomorph ⟨d.e x, hvalid x.property⟩)
  have himage (t : ℝ) (ht : t ∈ Icc (1 / 2 : ℝ) (13 / 16)) :
      f '' ball 0 (d.S.radial t) = W (c - h * t) := by
    have hint : interior (D t) = d.e '' ball 0 (d.S.radial t) :=
      d.ball_interior t (hlarge ht)
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have heint : d.e x ∈ interior (D t) := hint.symm ▸ ⟨x, hx, rfl⟩
      have hm : d.e x ∈ projectiveCoverDomain C2.puncture ∩
          P2.cover ⁻¹' W (c - h * t) := by
        rw [(hneg t ht).2]
        exact Or.inl heint
      exact hm.2
    · intro y hy
      have hs := hheight ht
      obtain ⟨_, hQsub, _, _, _⟩ := d.cuts (c - h * t) ((c - h * t + L) / 2)
        hs.1 (by linarith [hs.2]) (by linarith [hs.2])
      have hyQ : y ∈ Q (c - h * t) :=
        ⟨hy.1, fun hyV => hy.2 (interior_subset hyV)⟩
      obtain ⟨x, hx, hxy⟩ := P2.image_eq.symm.subset (hQsub hyQ)
      have hxW : x ∈ projectiveCoverDomain C2.puncture ∩ P2.cover ⁻¹' W (c - h * t) :=
        ⟨hx, by change P2.cover x ∈ W (c - h * t); rw [hxy]; exact hy⟩
      rcases (hneg t ht).2 ▸ hxW with hxint | ⟨z, hz, hzx⟩
      · obtain ⟨w, hw, hew⟩ := hint ▸ hxint
        exact ⟨w, hw, (congrArg P2.cover hew).trans hxy⟩
      · change -z = x at hzx
        have hnz : -z ∈ projectiveCoverDomain C2.puncture := by rw [hzx]; exact hx
        have hzD : z ∈ projectiveCoverDomain C2.puncture :=
          (neg_mem_projectiveCoverDomain_iff C2.puncture z).mp hnz
        have hzy : P2.cover z = y :=
          (StandardPuncturedProjectiveCover.cover_neg P2 hzD).symm.trans
            ((congrArg P2.cover hzx).trans hxy)
        obtain ⟨w, hw, hew⟩ := hint ▸ hz
        exact ⟨w, hw, (congrArg P2.cover hew).trans hzy⟩
  have hbij (x : E3) (hx : x ∈ ball 0 (d.S.radial (13 / 16))) :
      Function.Bijective (mfderiv (𝓡 3) (𝓡 3) f x) :=
    ((hlocal ⟨x, hx⟩).mfderivToContinuousLinearEquiv (by simp)).bijective
  obtain ⟨Phi, hPhi, hPhis, _⟩ :=
    PoincareConjecture.exists_partialDiffeomorph_of_injOn_of_nonsingular
      isOpen_ball hlocal.contMDiffOn hbij hinj
  let j0 := Phi.toOpenPartialHomeomorph
  have hj0s : j0.source = ball 0 (d.S.radial (13 / 16)) := hPhis
  have hj0f : (j0 : E3 → M) = f := hPhi
  let j := j0.restrOpen (ball 0 (d.S.radial (3 / 4))) isOpen_ball
  have hjs : j.source = ball 0 (d.S.radial (3 / 4)) := by
    change j0.source ∩ ball 0 (d.S.radial (3 / 4)) = _
    rw [hj0s, inter_eq_right.mpr (ball_subset_ball h0star.le)]
  have hjf : (j : E3 → M) = f := hj0f
  have hjt : j.target = W a := by
    rw [← j.image_source_eq_target, hjs, hjf]
    exact himage (3 / 4) (by norm_num)
  have hj : ContMDiffOn (𝓡 3) (𝓡 3) ∞ j j.source :=
    Phi.contMDiffOn_toFun.mono inter_subset_left
  have hji : ContMDiffOn (𝓡 3) (𝓡 3) ∞ j.symm j.target :=
    Phi.contMDiffOn_invFun.mono inter_subset_left
  have hnorm (q : UnitTwoSphere) (t : ℝ) (ht : t ∈ Ico (1 / 4 : ℝ) 1) :
      ‖d.S.radial t • (d.S.boundary_map q).val‖ = d.S.radial t := by
    rw [norm_smul, Real.norm_eq_abs,
      mem_sphere_zero_iff_norm.mp (d.S.boundary_map q).property, mul_one,
      abs_of_pos (d.S.radial_pos t ht)]
  have hfray (q : UnitTwoSphere) (t : ℝ) (ht : t ∈ Icc (1 / 2 : ℝ) (3 / 4)) :
      f (d.S.radial t • (d.S.boundary_map q).val) = N.coordinate_map (q, c - h * t) := by
    have ht' : t ∈ Icc (1 / 4 : ℝ) (7 / 8) := by
      constructor <;> linarith [ht.1, ht.2]
    have he := d.ray q t ht'
    rw [d.side_eq, neg_one_mul] at he
    change P2.cover (d.e _) = _
    rw [he]
    have hf := d.lift_eq (show (q, -t) ∈ univ ×ˢ Ioo (-1 : ℝ) 1 from
      ⟨mem_univ _, by constructor <;> linarith [ht.1, ht.2]⟩)
    simpa only [Function.comp_apply, mul_neg, ← sub_eq_add_neg] using hf
  have hjray (q : UnitTwoSphere) (t : ℝ) (ht : t ∈ Icc (1 / 2 : ℝ) (3 / 4)) :
      j (d.S.radial t • (d.S.boundary_map q).val) = N.coordinate_map (q, c - h * t) ∧
      j.symm (N.coordinate_map (q, c - h * t)) =
        d.S.radial t • (d.S.boundary_map q).val := by
    refine ⟨by rw [hjf]; exact hfray q t ht, ?_⟩
    have ht' : t ∈ Ico (1 / 4 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    have hx : d.S.radial t • (d.S.boundary_map q).val ∈ j0.source := by
      rw [hj0s, mem_ball_zero_iff, hnorm q t ht']
      exact d.S.radial_strictMono ht' (by norm_num) (by linarith [ht.2])
    have hi := j0.left_inv hx
    rw [hj0f] at hi
    change j0.symm (N.coordinate_map (q, c - h * t)) = _
    rw [← hfray q t ht]
    exact hi
  let A2 : Set E3 := {z | d.S.radial (1 / 2) < ‖z‖ ∧ ‖z‖ < d.S.radial (3 / 4)}
  obtain ⟨_, _, _, _, hcoords⟩ := d.cuts a b hva hab hbL
  have hannulus : f '' A2 = N.region a b := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      have hcont : ContinuousOn d.S.radial (Icc (1 / 2 : ℝ) (3 / 4)) :=
        (d.S.contDiffOn_radial d.collar (by norm_num)).continuousOn.mono
          (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      obtain ⟨t, ht, hrt⟩ := intermediate_value_Icc (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4)
        hcont (show ‖z‖ ∈ Icc (d.S.radial (1 / 2)) (d.S.radial (3 / 4)) from
          ⟨hz.1.le, hz.2.le⟩)
      have hto : t ∈ Ioo (1 / 2 : ℝ) (3 / 4) := by
        constructor
        · by_contra hnot
          have heq : t = 1 / 2 := le_antisymm (le_of_not_gt hnot) ht.1
          rw [heq] at hrt
          exact (ne_of_gt hz.1) hrt.symm
        · by_contra hnot
          have heq : t = 3 / 4 := le_antisymm ht.2 (le_of_not_gt hnot)
          rw [heq] at hrt
          exact (ne_of_lt hz.2) hrt.symm
      have ht' : t ∈ Ico (1 / 4 : ℝ) 1 := by
        constructor <;> linarith [hto.1, hto.2]
      have hr := d.S.radial_pos t ht'
      let q' : UnitTwoSphere := ⟨(d.S.radial t)⁻¹ • z, by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hr), ← hrt, inv_mul_cancel₀ hr.ne']⟩
      obtain ⟨q, hq⟩ := d.S.boundary_map.surjective q'
      change d.S.boundary_map q = q' at hq
      have hzq : d.S.radial t • (d.S.boundary_map q).val = z := by
        rw [hq]
        exact smul_inv_smul₀ hr.ne' z
      rw [hcoords]
      refine ⟨(q, c - h * t), ⟨mem_univ _, ?_, ?_⟩,
        (hfray q t ht).symm.trans (congrArg f hzq)⟩
      · dsimp only [a]
        nlinarith [hto.2]
      · dsimp only [b]
        nlinarith [hto.1]
    · intro y hy
      obtain ⟨⟨q, s⟩, hs, rfl⟩ := hcoords ▸ hy
      let t := (c - s) / h
      have hto : t ∈ Ioo (1 / 2 : ℝ) (3 / 4) := by
        constructor
        · apply (lt_div_iff₀ hh).mpr
          dsimp only [b] at hs
          linarith [hs.2.2]
        · apply (div_lt_iff₀ hh).mpr
          dsimp only [a] at hs
          linarith [hs.2.1]
      have ht' : t ∈ Ico (1 / 4 : ℝ) 1 := by
        constructor <;> linarith [hto.1, hto.2]
      have hcs : c - h * t = s := by dsimp [t]; field_simp; ring
      refine ⟨d.S.radial t • (d.S.boundary_map q).val, ?_, ?_⟩
      · change d.S.radial (1 / 2) < ‖_‖ ∧ ‖_‖ < d.S.radial (3 / 4)
        rw [hnorm q t ht']
        exact ⟨d.S.radial_strictMono (by norm_num) ht' hto.1,
          d.S.radial_strictMono ht' (by norm_num) hto.2⟩
      · simpa only [hcs] using hfray q t ⟨hto.1.le, hto.2.le⟩
  have hannulus' : j.symm '' N.region a b = A2 := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hannulus.symm ▸ hx
      have hzj : z ∈ j.source := hjs.symm ▸ mem_ball_zero_iff.mpr hz.2
      rw [← hjf, j.left_inv hzj]
      exact hz
    · intro z hz
      have hzj : z ∈ j.source := hjs.symm ▸ mem_ball_zero_iff.mpr hz.2
      refine ⟨f z, hannulus ▸ mem_image_of_mem f hz, ?_⟩
      rw [← hjf, j.left_inv hzj]
  exact ⟨j.symm, hjt, hjs, hji, hj, hjf, hjray, hannulus'⟩

end PoincareConjecture.M25.Topology3D
