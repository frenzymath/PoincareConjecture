import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.MetricSpace.HausdorffDimension









set_option autoImplicit false

open Set Metric Topology
open scoped unitInterval ContDiff

namespace Poincare.Topology


theorem exists_contDiff_approx_preserving_value
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : V → E} (hf : Continuous f) (x : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : V → E, ContDiff ℝ ∞ h ∧ (∀ z, dist (h z) (f z) < ε) ∧
      ∀ z, f z = x → h z = x := by
  have hf' : Continuous (fun z => f z - x) := hf.sub continuous_const
  obtain ⟨g, hg, hdist, hsupp⟩ := hf'.exists_contDiff_approx (⊤ : ℕ∞)
    (ε := fun _ => ε) continuous_const (fun _ => hε)
  refine ⟨fun z => g z + x, hg.add contDiff_const, ?_, ?_⟩
  · intro z
    calc
      dist (g z + x) (f z) = dist (g z + x) ((f z - x) + x) := by
        rw [sub_add_cancel]
      _ = dist (g z) (f z - x) := dist_add_right _ _ _
      _ < ε := hdist z
  · intro z hz
    have hgz : g z = 0 := by
      by_contra hne
      have hmem := hsupp (show z ∈ Function.support g from hne)
      exact hmem (sub_eq_zero.mpr hz)
    simp only [hgz, zero_add]


theorem exists_sphere_point_not_normalized_range
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (h : V → E) (hh : ContDiff ℝ 1 h)
    (hdim : Module.finrank ℝ V + 1 < Module.finrank ℝ E) :
    ∃ v : sphere (0 : E) 1, ∀ z, NormedSpace.normalize (h z) ≠ (v : E) := by
  let F : ℝ × V → E := fun z => z.1 • h z.2
  have hF : ContDiff ℝ 1 F := contDiff_fst.smul (hh.comp contDiff_snd)
  have hdim' : Module.finrank ℝ (ℝ × V) < Module.finrank ℝ E := by
    simpa only [Module.finrank_prod, Module.finrank_self, Nat.add_comm 1] using hdim
  obtain ⟨w, hw⟩ := (hF.dense_compl_range_of_finrank_lt_finrank hdim').nonempty
  have hwzero : w ≠ 0 := by
    intro hzero
    apply hw
    exact ⟨(0, 0), by simp only [F, zero_smul, hzero]⟩
  refine ⟨⟨NormedSpace.normalize w, ?_⟩, ?_⟩
  · exact mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hwzero)
  · intro z hz
    apply hw
    refine ⟨(‖w‖ * ‖h z‖⁻¹, z), ?_⟩
    change (‖w‖ * ‖h z‖⁻¹) • h z = w
    calc
      (‖w‖ * ‖h z‖⁻¹) • h z = ‖w‖ • NormedSpace.normalize (h z) := by
        rw [NormedSpace.normalize, mul_smul]
      _ = ‖w‖ • NormedSpace.normalize w := congrArg (fun a => ‖w‖ • a) hz
      _ = w := NormedSpace.norm_smul_normalize w



theorem sphere_genLoop_homotopic_const_of_avoids
    {N E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : sphere (0 : E) 1} (v : sphere (0 : E) 1) (hx : x ≠ v)
    (p : GenLoop N (sphere (0 : E) 1) x) (hp : ∀ t, p t ≠ v) :
    GenLoop.Homotopic p GenLoop.const := by
  let e := stereographic (norm_eq_of_mem_sphere v)
  have htarget : e.target = univ := stereographic_target _
  have hxsource : x ∈ e.source := by
    simpa only [e, stereographic_source, mem_compl_iff, mem_singleton_iff] using hx
  have hpsource (t : I^N) : p t ∈ e.source := by
    simpa only [e, stereographic_source, mem_compl_iff, mem_singleton_iff] using hp t
  let f : C(I^N, (ℝ ∙ (v : E))ᗮ) :=
    ⟨fun t => e (p t), e.continuousOn.comp_continuous p.val.continuous hpsource⟩
  let H := ContinuousMap.Homotopy.affine f (ContinuousMap.const _ (e x))
  have hinverse : Continuous e.symm := by
    have he := e.continuousOn_symm
    rw [htarget] at he
    exact continuousOn_univ.mp he
  refine ⟨{
    toFun := fun z => e.symm (H z)
    continuous_toFun := hinverse.comp H.continuous
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    change e.symm (H (0, t)) = p t
    rw [H.apply_zero]
    exact e.left_inv (hpsource t)
  · intro t
    change e.symm (H (1, t)) = x
    rw [H.apply_one]
    exact e.left_inv hxsource
  · intro t a ha
    change e.symm (AffineMap.lineMap (e (p a)) (e x) (t : ℝ)) = p a
    rw [GenLoop.boundary p a ha, AffineMap.lineMap_same_apply]
    exact e.left_inv hxsource



theorem sphere_genLoop_homotopic_const_of_dim_lt
    {N E : Type*} [Fintype N] [Nonempty N]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Fintype.card N + 1 < Module.finrank ℝ E)
    {x : sphere (0 : E) 1} (p : GenLoop N (sphere (0 : E) 1) x) :
    GenLoop.Homotopic p GenLoop.const := by
  let r : (N → ℝ) → I^N := fun z i => projIcc 0 1 zero_le_one (z i)
  have hr : Continuous r :=
    continuous_pi fun i => continuous_projIcc.comp (continuous_apply i)
  have hret (t : I^N) : r (fun i => (t i : ℝ)) = t := by
    funext i
    exact projIcc_val zero_le_one (t i)
  let f : (N → ℝ) → E := fun z => p (r z)
  have hf : Continuous f := continuous_subtype_val.comp (p.val.continuous.comp hr)
  obtain ⟨h, hh, hdist, hfix⟩ :=
    exists_contDiff_approx_preserving_value hf (x : E) (ε := 1 / 2) (by norm_num)
  let hc : C(I^N, E) :=
    ⟨fun t => h (fun i => (t i : ℝ)),
      hh.continuous.comp (continuous_pi fun i =>
        continuous_subtype_val.comp (continuous_apply i))⟩
  have hboundary (t : I^N) (ht : t ∈ Cube.boundary N) : hc t = (x : E) := by
    apply hfix
    change (p (r (fun i => (t i : ℝ))) : E) = (x : E)
    rw [hret, GenLoop.boundary p t ht]
  have hclose (t : I^N) : dist (hc t) (p t : E) < 1 := by
    have hd := hdist (fun i => (t i : ℝ))
    change dist (hc t) (p (r (fun i => (t i : ℝ))) : E) < 1 / 2 at hd
    rw [hret] at hd
    exact hd.trans (by norm_num)
  let pE : C(I^N, E) :=
    ⟨fun t => (p t : E), continuous_subtype_val.comp p.val.continuous⟩
  let H := ContinuousMap.Homotopy.affine pE hc
  have hH (z : unitInterval × I^N) : H z ≠ 0 := by
    have hd : dist (H z) (p z.2 : E) < 1 := by
      change dist (AffineMap.lineMap (p z.2 : E) (hc z.2) (z.1 : ℝ)) (p z.2 : E) < 1
      rw [dist_lineMap_left, Real.norm_of_nonneg z.1.2.1, dist_comm (p z.2 : E) (hc z.2)]
      exact (mul_le_of_le_one_left dist_nonneg z.1.2.2).trans_lt (hclose z.2)
    intro hzero
    simp only [hzero, dist_zero_left, norm_eq_of_mem_sphere, lt_self_iff_false] at hd
  have hhc (t : I^N) : hc t ≠ 0 := by
    simpa only [H.apply_one] using hH (1, t)
  have hunit (t : I^N) : NormedSpace.normalize (hc t) ∈ sphere (0 : E) 1 :=
    mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize (hhc t))
  have hunitH (z : unitInterval × I^N) :
      NormedSpace.normalize (H z) ∈ sphere (0 : E) 1 :=
    mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize (hH z))
  have hcont : Continuous (fun t => NormedSpace.normalize (hc t)) :=
    (hc.continuous.norm.inv₀ (fun t => norm_ne_zero_iff.mpr (hhc t))).smul hc.continuous
  have hcontH : Continuous (fun z => NormedSpace.normalize (H z)) :=
    (H.continuous.norm.inv₀ (fun z => norm_ne_zero_iff.mpr (hH z))).smul H.continuous
  let q : GenLoop N (sphere (0 : E) 1) x :=
    ⟨⟨fun t => ⟨NormedSpace.normalize (hc t), hunit t⟩, hcont.subtype_mk hunit⟩, by
      intro t ht
      apply Subtype.ext
      change NormedSpace.normalize (hc t) = (x : E)
      rw [hboundary t ht]
      exact NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere x)⟩
  have hpq : GenLoop.Homotopic p q := by
    refine ⟨{
      toFun := fun z => ⟨NormedSpace.normalize (H z), hunitH z⟩
      continuous_toFun := hcontH.subtype_mk hunitH
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro t
      apply Subtype.ext
      change NormedSpace.normalize (H (0, t)) = (p t : E)
      rw [H.apply_zero]
      exact NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere (p t))
    · intro t
      apply Subtype.ext
      change NormedSpace.normalize (H (1, t)) = NormedSpace.normalize (hc t)
      rw [H.apply_one]
    · intro t a ha
      apply Subtype.ext
      change NormedSpace.normalize (AffineMap.lineMap (p a : E) (hc a) (t : ℝ)) = (p a : E)
      rw [hboundary a ha, GenLoop.boundary p a ha, AffineMap.lineMap_same_apply]
      exact NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere x)
  obtain ⟨v, hv⟩ := exists_sphere_point_not_normalized_range h (hh.of_le (by simp))
    (by simpa only [Module.finrank_fintype_fun_eq_card] using hdim)
  have havoid (t : I^N) : q t ≠ v := by
    intro heq
    exact hv (fun i => (t i : ℝ)) (congrArg Subtype.val heq)
  have hx : x ≠ v := by
    intro heq
    apply havoid (fun _ => 0)
    exact (GenLoop.boundary q _
      ⟨Classical.choice (inferInstance : Nonempty N), Or.inl rfl⟩).trans heq
  exact hpq.trans (sphere_genLoop_homotopic_const_of_avoids v hx q havoid)


theorem sphere_homotopyGroup_subsingleton_of_dim_lt
    {N E : Type*} [Fintype N] [Nonempty N]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Fintype.card N + 1 < Module.finrank ℝ E)
    (x : sphere (0 : E) 1) :
    Subsingleton (HomotopyGroup N (sphere (0 : E) 1) x) := by
  refine ⟨fun a b => Quotient.inductionOn₂ a b ?_⟩
  intro p q
  exact Quotient.sound ((sphere_genLoop_homotopic_const_of_dim_lt hdim p).trans
    (sphere_genLoop_homotopic_const_of_dim_lt hdim q).symm)



theorem sphere_simplyConnectedSpace_of_two_lt_finrank
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : 2 < Module.finrank ℝ E) :
    SimplyConnectedSpace (sphere (0 : E) 1) := by
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨?_, ?_⟩
  · exact isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank (by omega)) (0 : E) zero_le_one)
  · intro x p
    let : Subsingleton (HomotopyGroup.Pi 1 (sphere (0 : E) 1) x) :=
      sphere_homotopyGroup_subsingleton_of_dim_lt (N := Fin 1)
        (by simpa only [Fintype.card_fin] using hdim) x
    let e := HomotopyGroup.pi1EquivFundamentalGroup (X := sphere (0 : E) 1) (x := x)
    have heq : (⟦p⟧ : FundamentalGroup (sphere (0 : E) 1) x) = ⟦Path.refl x⟧ :=
      e.symm.injective (Subsingleton.elim _ _)
    exact Quotient.exact heq

end Poincare.Topology
