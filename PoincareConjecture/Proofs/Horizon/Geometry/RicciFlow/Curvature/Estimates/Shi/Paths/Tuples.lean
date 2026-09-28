import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Frames.Bounded
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Coordinates.EndpointJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Coordinates.Normal
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Paths.JoinedDensity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Paths.JoinedVariation












set_option autoImplicit false

open Set Filter Function
open scoped Topology Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {m N : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "End" => E →L[ℝ] E
local notation "Data" => ℝ × ((E × (E × End)) × ((E × End) × (E × End)))

noncomputable def shiPathTime (N k : ℕ) : ℝ := (k : ℝ) / (N : ℝ)

@[simp] theorem shiPathTime_zero (N : ℕ) : shiPathTime N 0 = 0 := by
  simp [shiPathTime]

@[simp] theorem shiPathTime_last (hN : 0 < N) : shiPathTime N N = 1 := by
  exact div_self (by exact_mod_cast (ne_of_gt hN))

theorem shiPathTime_step (hN : 0 < N) (k : ℕ) :
    shiPathTime N k < shiPathTime N (k + 1) := by
  apply div_lt_div_of_pos_right _ (by exact_mod_cast hN)
  exact_mod_cast Nat.lt_succ_self k

def shiPathExtendedChart (c : Fin m → OpenPartialHomeomorph M E)
    (cstar : OpenPartialHomeomorph M E) : Sum (Fin m) Unit → OpenPartialHomeomorph M E :=
  Sum.elim c (fun _ => cstar)

def shiPathExtendedCore (K : Fin m → Set M) (q : M) : Sum (Fin m) Unit → Set M :=
  Sum.elim K (fun _ => {q})

def shiPathVertexLabel (label : Fin N → Fin m) (k : Fin (N + 1)) : Sum (Fin m) Unit :=
  if h : k.val < N then Sum.inl (label ⟨k.val, h⟩) else Sum.inr ()

def shiPathVertexChart (c : Fin m → OpenPartialHomeomorph M E)
    (cstar : OpenPartialHomeomorph M E) (label : Fin N → Fin m) (k : Fin (N + 1)) :
    OpenPartialHomeomorph M E :=
  shiPathExtendedChart c cstar (shiPathVertexLabel label k)

noncomputable def shiPathVertexFrame (P : Fin N → ℝ → End) (k : Fin (N + 1)) : End :=
  if h : k.val < N then P ⟨k.val, h⟩ (shiPathTime N k.val)
    else ContinuousLinearMap.id ℝ E

noncomputable def shiPathVertexCoordinate (c : Fin m → OpenPartialHomeomorph M E)
    (cstar : OpenPartialHomeomorph M E) (label : Fin N → Fin m)
    (γ : ℝ → M) (k : Fin (N + 1)) : E :=
  shiPathVertexChart c cstar label k (γ (shiPathTime N k.val))

noncomputable def shiPathTuple (c : Fin m → OpenPartialHomeomorph M E)
    (cstar : OpenPartialHomeomorph M E) (label : Fin N → Fin m)
    (γ : ℝ → M) (P : Fin N → ℝ → End) (j : Fin N) (t : ℝ) : Data :=
  (t, ((c (label j) (γ t), (deriv ((c (label j)) ∘ γ) t, P j t)),
    ((shiPathVertexCoordinate c cstar label γ j.castSucc, shiPathVertexFrame P j.castSucc),
      (shiPathVertexCoordinate c cstar label γ j.succ, shiPathVertexFrame P j.succ))))

noncomputable def shiPathVertexMap (D : LeviCivitaData g)
    (c : Fin m → OpenPartialHomeomorph M E) (cstar : OpenPartialHomeomorph M E)
    (label : Fin N → Fin m) (γ : ℝ → M) (P : Fin N → ℝ → End)
    (k : Fin (N + 1)) (z : E) : M :=
  (shiPathVertexChart c cstar label k).symm
    (shiRawCoordinateVariation D (shiPathVertexChart c cstar label k)
      (shiPathTime N k.val) (shiPathVertexCoordinate c cstar label γ k)
      (shiPathVertexFrame P k) z)

noncomputable def shiPathEndpoint (D : LeviCivitaData g)
    (c : Fin m → OpenPartialHomeomorph M E) (cstar : OpenPartialHomeomorph M E)
    (label : Fin N → Fin m) (γ : ℝ → M) (P : Fin N → ℝ → End)
    (j : Fin N) (k : Fin (N + 1)) (z : E) : E :=
  c (label j) (shiPathVertexMap D c cstar label γ P k z)

noncomputable def shiPathJoinedVariation (D : LeviCivitaData g)
    (c : Fin m → OpenPartialHomeomorph M E) (cstar : OpenPartialHomeomorph M E)
    (label : Fin N → Fin m) (γ : ℝ → M) (P : Fin N → ℝ → End)
    (j : Fin N) : ℝ → E → E :=
  joinedCoordinateVariation (shiPathTime N j.val) (shiPathTime N (j.val + 1))
    ((c (label j)) ∘ γ) (fun t => t • P j t)
    (fun t => -(shiChartChristoffel D (c (label j)) (c (label j) (γ t))).bilinearComp
      (t • P j t) (t • P j t))
    (shiPathEndpoint D c cstar label γ P j j.castSucc)
    (shiPathEndpoint D c cstar label γ P j j.succ)

noncomputable def shiPathManifoldSegment (D : LeviCivitaData g)
    (c : Fin m → OpenPartialHomeomorph M E) (cstar : OpenPartialHomeomorph M E)
    (label : Fin N → Fin m) (γ : ℝ → M) (P : Fin N → ℝ → End)
    (j : Fin N) (z : E) (t : ℝ) : M :=
  (c (label j)).symm (shiPathJoinedVariation D c cstar label γ P j t z)

theorem shiPathExtended_data [T2Space M]
    (c : Fin m → OpenPartialHomeomorph M E) (cstar : OpenPartialHomeomorph M E)
    (K : Fin m → Set M) (q : M)
    (hK : ∀ i, IsCompact (K i)) (hKs : ∀ i, K i ⊆ (c i).source)
    (hc : ∀ i, ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ (c i) (c i).source)
    (hi : ∀ i, ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (c i).symm (c i).target)
    (hq : q ∈ cstar.source)
    (hstar : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cstar cstar.source)
    (hstari : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cstar.symm cstar.target)
    (i : Sum (Fin m) Unit) :
    IsCompact (shiPathExtendedCore K q i) ∧
      shiPathExtendedCore K q i ⊆ (shiPathExtendedChart c cstar i).source ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ (shiPathExtendedChart c cstar i)
        (shiPathExtendedChart c cstar i).source ∧
      ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (shiPathExtendedChart c cstar i).symm
        (shiPathExtendedChart c cstar i).target := by
  rcases i with i | i
  · exact ⟨hK i, hKs i, hc i, hi i⟩
  · exact ⟨isCompact_singleton, singleton_subset_iff.mpr hq, hstar, hstari⟩

theorem shiPath_vertex_core_and_bound
    (hN : 0 < N) (K : Fin m → Set M) (q : M) (label : Fin N → Fin m)
    (γ : ℝ → M) (P : Fin N → ℝ → End) (hγ1 : γ 1 = q)
    (hinside : ∀ j : Fin N, MapsTo γ
      (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) (interior (K (label j))))
    {L : ℝ} (hL : 1 ≤ L)
    (hP : ∀ j t, t ∈ Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1)) →
      ‖P j t‖ ≤ L) (k : Fin (N + 1)) :
    γ (shiPathTime N k.val) ∈ shiPathExtendedCore K q (shiPathVertexLabel label k) ∧
      ‖shiPathVertexFrame P k‖ ≤ L := by
  by_cases hk : k.val < N
  · simp only [shiPathVertexLabel, shiPathVertexFrame, dif_pos hk]
    exact ⟨interior_subset (hinside ⟨k.val, hk⟩
      ⟨le_rfl, (shiPathTime_step hN k.val).le⟩),
      hP ⟨k.val, hk⟩ _ ⟨le_rfl, (shiPathTime_step hN k.val).le⟩⟩
  · have hkN : k.val = N := by omega
    simp only [shiPathVertexLabel, shiPathVertexFrame, dif_neg hk]
    constructor
    · simpa only [shiPathExtendedCore, Sum.elim_inr, hkN, shiPathTime_last hN, hγ1]
        using (mem_singleton q)
    · exact ContinuousLinearMap.norm_id_le.trans hL

theorem shiPath_vertex_source
    (hN : 0 < N) (c : Fin m → OpenPartialHomeomorph M E)
    (cstar : OpenPartialHomeomorph M E) (label : Fin N → Fin m) (γ : ℝ → M)
    (hinside : ∀ j : Fin N, MapsTo γ
      (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) (c (label j)).source)
    (hstar : γ 1 ∈ cstar.source) (k : Fin (N + 1)) :
    γ (shiPathTime N k.val) ∈ (shiPathVertexChart c cstar label k).source := by
  by_cases hk : k.val < N
  · simp only [shiPathVertexChart, shiPathVertexLabel, dif_pos hk,
      shiPathExtendedChart, Sum.elim_inl]
    exact hinside ⟨k.val, hk⟩ ⟨le_rfl, (shiPathTime_step hN k.val).le⟩
  · have hkN : k.val = N := by omega
    have hk' : k = Fin.last N := Fin.ext hkN
    subst k
    simpa only [shiPathVertexChart, shiPathVertexLabel, dif_neg (Nat.lt_irrefl N),
      Fin.val_last, shiPathExtendedChart, Sum.elim_inr, shiPathTime_last hN] using hstar

theorem shiPathVertexChart_smooth
    (c : Fin m → OpenPartialHomeomorph M E) (cstar : OpenPartialHomeomorph M E)
    (label : Fin N → Fin m)
    (hc : ∀ i, ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ (c i) (c i).source)
    (hi : ∀ i, ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (c i).symm (c i).target)
    (hstar : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cstar cstar.source)
    (hstari : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cstar.symm cstar.target)
    (k : Fin (N + 1)) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ (shiPathVertexChart c cstar label k)
      (shiPathVertexChart c cstar label k).source ∧
    ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (shiPathVertexChart c cstar label k).symm
      (shiPathVertexChart c cstar label k).target := by
  by_cases hk : k.val < N
  · simpa only [shiPathVertexChart, shiPathVertexLabel, dif_pos hk,
      shiPathExtendedChart, Sum.elim_inl] using
      And.intro (hc (label ⟨k.val, hk⟩)) (hi (label ⟨k.val, hk⟩))
  · simpa only [shiPathVertexChart, shiPathVertexLabel, dif_neg hk,
      shiPathExtendedChart, Sum.elim_inr] using And.intro hstar hstari

theorem shiPath_coordinate_regular
    {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ)
    {a b : ℝ} (hab : a < b) (hinside : MapsTo γ (Icc a b) c.source) :
    ContDiffOn ℝ 1 (c ∘ γ) (Icc a b) ∧
      ContinuousOn (deriv (c ∘ γ)) (Icc a b) ∧
      ∀ t ∈ Icc a b, derivWithin (c ∘ γ) (Icc a b) t = deriv (c ∘ γ) t := by
  let U : Set ℝ := γ ⁻¹' c.source
  have hU : IsOpen U := c.open_source.preimage hγ.continuous
  have h1 : (1 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hx : ContDiffOn ℝ 1 (c ∘ γ) U :=
    ((hc.of_le h1).comp hγ.contMDiffOn (fun _ ht => ht)).contDiffOn
  refine ⟨hx.mono hinside, (hx.continuousOn_deriv_of_isOpen hU le_rfl).mono hinside, ?_⟩
  intro t ht
  exact (((hx.contDiffAt (hU.mem_nhds (hinside ht))).differentiableAt
    (by norm_num)).hasDerivAt.hasDerivWithinAt).derivWithin
      ((uniqueDiffOn_Icc hab).uniqueDiffWithinAt ht)

set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
theorem shiPathTuple_compact_membership [T2Space M]
    (hN : 0 < N) (c : Fin m → OpenPartialHomeomorph M E)
    (cstar : OpenPartialHomeomorph M E) (K : Fin m → Set M)
    (hK : ∀ i, IsCompact (K i)) (hKs : ∀ i, K i ⊆ (c i).source)
    (hc : ∀ i, ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ (c i) (c i).source)
    (hi : ∀ i, ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (c i).symm (c i).target)
    (q : M) (hq : q ∈ cstar.source)
    (hstar : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cstar cstar.source)
    (hstari : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cstar.symm cstar.target)
    (label : Fin N → Fin m) (γ : ℝ → M) (P : Fin N → ℝ → End)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ) (hγ1 : γ 1 = q)
    (hinside : ∀ j : Fin N, MapsTo γ
      (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) (interior (K (label j))))
    (hPC : ∀ j, ContDiffOn ℝ 1 (P j)
      (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))))
    {L R : ℝ} (hL : 1 ≤ L)
    (hP : ∀ j t, t ∈ Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1)) →
      ‖P j t‖ ≤ L)
    (hT : ∀ j t, t ∈ Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1)) →
      ‖deriv ((c (label j)) ∘ γ) t‖ ≤ L * R)
    (j : Fin N) :
    let cL := shiPathVertexChart c cstar label j.castSucc
    let cR := shiPathVertexChart c cstar label j.succ
    let H := c (label j) '' K (label j)
    let HL := cL '' (K (label j) ∩ shiPathExtendedCore K q (shiPathVertexLabel label j.castSucc))
    let HR := cR '' (K (label j) ∩ shiPathExtendedCore K q (shiPathVertexLabel label j.succ))
    IsCompact H ∧ IsCompact HL ∧ IsCompact HR ∧ H ⊆ (c (label j)).target ∧
      HL ⊆ cL.target ∩ cL.symm ⁻¹' (c (label j)).source ∧
      HR ⊆ cR.target ∩ cR.symm ⁻¹' (c (label j)).source ∧
      ContinuousOn (shiPathTuple c cstar label γ P j)
        (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) ∧
      MapsTo (shiPathTuple c cstar label γ P j)
        (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1)))
        (shiJoinedCompactTuples (shiPathTime N j.val) (shiPathTime N (j.val + 1))
          L R H HL HR) := by
  have hv (k : Fin (N + 1)) := shiPath_vertex_core_and_bound hN K q label γ P hγ1 hinside hL hP k
  have he (k : Fin (N + 1)) := shiPathExtended_data c cstar K q hK hKs hc hi hq hstar hstari
    (shiPathVertexLabel label k)
  have hsets := shiJoinedCore_coordinate_sets (c (label j))
    (shiPathVertexChart c cstar label j.castSucc) (shiPathVertexChart c cstar label j.succ)
    (hK (label j)) (he j.castSucc).1 (he j.succ).1
    (hKs (label j)) (he j.castSucc).2.1 (he j.succ).2.1
  refine ⟨hsets.1, hsets.2.1, hsets.2.2.1, hsets.2.2.2.1,
    hsets.2.2.2.2.1, hsets.2.2.2.2.2, ?_, ?_⟩
  · have hcoord := shiPath_coordinate_regular (hc (label j)) hγ (shiPathTime_step hN j.val)
      (fun t ht => hKs (label j) (interior_subset (hinside j ht)))
    have hleft : ContinuousOn
        (fun _ : ℝ =>
          (shiPathVertexCoordinate c cstar label γ j.castSucc,
            shiPathVertexFrame P j.castSucc))
        (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) :=
      continuousOn_const.prodMk continuousOn_const
    have hright : ContinuousOn
        (fun _ : ℝ =>
          (shiPathVertexCoordinate c cstar label γ j.succ,
            shiPathVertexFrame P j.succ))
        (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) :=
      continuousOn_const.prodMk continuousOn_const
    exact continuousOn_id.prodMk
      ((hcoord.1.continuousOn.prodMk (hcoord.2.1.prodMk (hPC j).continuousOn)).prodMk
        (hleft.prodMk hright))
  · intro t ht
    have hl : γ (shiPathTime N j.val) ∈ K (label j) :=
      interior_subset (hinside j ⟨le_rfl, (shiPathTime_step hN j.val).le⟩)
    have hr : γ (shiPathTime N (j.val + 1)) ∈ K (label j) :=
      interior_subset (hinside j ⟨(shiPathTime_step hN j.val).le, le_rfl⟩)
    refine ⟨ht, ⟨mem_image_of_mem _ (interior_subset (hinside j ht)),
      ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simpa only [shiPathTuple, Metric.mem_closedBall, dist_zero_right] using hT j t ht
    · simpa only [shiPathTuple, Metric.mem_closedBall, dist_zero_right] using hP j t ht
    · exact mem_image_of_mem _ ⟨hl, (hv j.castSucc).1⟩
    · simpa only [shiPathTuple, Metric.mem_closedBall, dist_zero_right] using (hv j.castSucc).2
    · exact mem_image_of_mem _ ⟨hr, (hv j.succ).1⟩
    · simpa only [shiPathTuple, Metric.mem_closedBall, dist_zero_right] using (hv j.succ).2

set_option backward.isDefEq.respectTransparency false in
theorem shiPath_vertex_physical_match
    (hN : 0 < N) (c : Fin m → OpenPartialHomeomorph M E)
    (cstar : OpenPartialHomeomorph M E) (label : Fin N → Fin m)
    (γ : ℝ → M) (P : Fin N → ℝ → End)
    (hstar : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cstar cstar.source)
    (hstari : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cstar.symm cstar.target)
    (hq : γ 1 ∈ cstar.source) (J : E ≃L[ℝ] TangentSpace (𝓡 n) (γ 1))
    (hd : mvfderiv (𝓡 n) cstar (γ 1) = (J.symm : TangentSpace (𝓡 n) (γ 1) →L[ℝ] E))
    (hjoin : ∀ (j : ℕ) (hj : j + 1 < N) (v : E),
      shiChartField (c (label ⟨j, (Nat.lt_succ_self j).trans hj⟩))
          (P ⟨j, (Nat.lt_succ_self j).trans hj⟩ (shiPathTime N (j + 1)) v)
          (γ (shiPathTime N (j + 1))) =
        shiChartField (c (label ⟨j + 1, hj⟩))
          (P ⟨j + 1, hj⟩ (shiPathTime N (j + 1)) v) (γ (shiPathTime N (j + 1))))
    (hend : ∀ j : Fin N, j.val + 1 = N → ∀ v,
      shiChartField (c (label j)) (P j 1 v) (γ 1) = J v)
    (j : Fin N) :
    (∀ v, shiChartField (c (label j)) (P j (shiPathTime N j.val) v)
      (γ (shiPathTime N j.val)) =
        shiChartField (shiPathVertexChart c cstar label j.castSucc)
          (shiPathVertexFrame P j.castSucc v) (γ (shiPathTime N j.val))) ∧
    (∀ v, shiChartField (c (label j)) (P j (shiPathTime N (j.val + 1)) v)
      (γ (shiPathTime N (j.val + 1))) =
        shiChartField (shiPathVertexChart c cstar label j.succ)
          (shiPathVertexFrame P j.succ v) (γ (shiPathTime N (j.val + 1)))) := by
  constructor
  · intro v
    simp [shiPathVertexChart, shiPathVertexLabel, shiPathExtendedChart,
      shiPathVertexFrame, j.isLt]
  · intro v
    by_cases hj : j.val + 1 < N
    · simpa [shiPathVertexChart, shiPathVertexLabel, shiPathExtendedChart,
        shiPathVertexFrame, hj] using hjoin j.val hj v
    · have hjN : j.val + 1 = N := by omega
      have he := (hend j hjN v).trans
        (shiNormalChartField_at_base hstar hstari hq J hd v).symm
      have htime : shiPathTime N (j.val + 1) = 1 := by
        rw [hjN, shiPathTime_last hN]
      rw [htime]
      simpa [shiPathVertexChart, shiPathVertexLabel, shiPathExtendedChart,
        shiPathVertexFrame, hj, hjN, shiPathTime_last hN] using he

private theorem path_endpoint_source
    (hN : 0 < N) (c : Fin m → OpenPartialHomeomorph M E)
    (cstar : OpenPartialHomeomorph M E) (label : Fin N → Fin m) (γ : ℝ → M)
    (hinside : ∀ j : Fin N, MapsTo γ
      (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) (c (label j)).source)
    (hstar : γ 1 ∈ cstar.source) (j : Fin N) (k : Fin (N + 1))
    (hk : k = j.castSucc ∨ k = j.succ) :
    γ (shiPathTime N k.val) ∈ (c (label j)).source ∧
      γ (shiPathTime N k.val) ∈ (shiPathVertexChart c cstar label k).source := by
  refine ⟨?_, shiPath_vertex_source hN c cstar label γ hinside hstar k⟩
  rcases hk with rfl | rfl
  · exact hinside j ⟨le_rfl, (shiPathTime_step hN j.val).le⟩
  · exact hinside j ⟨(shiPathTime_step hN j.val).le, le_rfl⟩

set_option maxHeartbeats 1800000 in

set_option synthInstance.maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency false in
theorem shiPathEndpoint_transition_jets [T2Space M] (D : LeviCivitaData g)
    (hN : 0 < N) (c : Fin m → OpenPartialHomeomorph M E)
    (cstar : OpenPartialHomeomorph M E) (label : Fin N → Fin m)
    (γ : ℝ → M) (P : Fin N → ℝ → End)
    (hc : ∀ i, ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ (c i) (c i).source)
    (hi : ∀ i, ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (c i).symm (c i).target)
    (hinside : ∀ j : Fin N, MapsTo γ
      (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) (c (label j)).source)
    (hstar : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cstar cstar.source)
    (hstari : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cstar.symm cstar.target)
    (hq : γ 1 ∈ cstar.source) (J : E ≃L[ℝ] TangentSpace (𝓡 n) (γ 1))
    (hd : mvfderiv (𝓡 n) cstar (γ 1) = (J.symm : TangentSpace (𝓡 n) (γ 1) →L[ℝ] E))
    (hjoin : ∀ (j : ℕ) (hj : j + 1 < N) (v : E),
      shiChartField (c (label ⟨j, (Nat.lt_succ_self j).trans hj⟩))
          (P ⟨j, (Nat.lt_succ_self j).trans hj⟩ (shiPathTime N (j + 1)) v)
          (γ (shiPathTime N (j + 1))) =
        shiChartField (c (label ⟨j + 1, hj⟩))
          (P ⟨j + 1, hj⟩ (shiPathTime N (j + 1)) v) (γ (shiPathTime N (j + 1))))
    (hend : ∀ j : Fin N, j.val + 1 = N → ∀ v,
      shiChartField (c (label j)) (P j 1 v) (γ 1) = J v)
    (j : Fin N) (k : Fin (N + 1)) (hk : k = j.castSucc ∨ k = j.succ) :
    let s := shiPathTime N k.val
    let Y := shiPathVertexCoordinate c cstar label γ k
    let A := s • P j s
    let B := -(shiChartChristoffel D (c (label j)) (c (label j) (γ s))).bilinearComp A A
    P j s = (fderiv ℝ ((c (label j)) ∘ (shiPathVertexChart c cstar label k).symm) Y).comp
      (shiPathVertexFrame P k) ∧
      ContDiffAt ℝ ∞ (shiPathEndpoint D c cstar label γ P j k) 0 ∧
      shiPathEndpoint D c cstar label γ P j k 0 = c (label j) (γ s) ∧
      fderiv ℝ (shiPathEndpoint D c cstar label γ P j k) 0 = A ∧
      fderiv ℝ (fderiv ℝ (shiPathEndpoint D c cstar label γ P j k)) 0 = B := by
  have hsrc := path_endpoint_source hN c cstar label γ hinside hq j k hk
  have hvc := shiPathVertexChart_smooth c cstar label hc hi hstar hstari k
  have hInv : (shiPathVertexChart c cstar label k).symm
      (shiPathVertexCoordinate c cstar label γ k) = γ (shiPathTime N k.val) :=
    (shiPathVertexChart c cstar label k).left_inv hsrc.2
  have hmatch : ∀ v, shiChartField (c (label j)) (P j (shiPathTime N k.val) v)
      (γ (shiPathTime N k.val)) =
        shiChartField (shiPathVertexChart c cstar label k)
          (shiPathVertexFrame P k v) (γ (shiPathTime N k.val)) := by
    have hm := shiPath_vertex_physical_match hN c cstar label γ P hstar hstari hq J hd hjoin hend j
    rcases hk with rfl | rfl
    · exact hm.1
    · exact hm.2
  have hy : shiPathVertexCoordinate c cstar label γ k ∈
      (shiPathVertexChart c cstar label k).target :=
    (shiPathVertexChart c cstar label k).map_source hsrc.2
  have hnew : (shiPathVertexChart c cstar label k).symm
      (shiPathVertexCoordinate c cstar label γ k) ∈ (c (label j)).source := by
    rw [hInv]
    exact hsrc.1
  have hP := shiEndpoint_frame_transition hvc.1 hvc.2 (hc (label j)) (hi (label j)) hy hnew
    (Pold := shiPathVertexFrame P k) (Pnew := P j (shiPathTime N k.val))
    (by intro v; rw [hInv]; exact hmatch v)
  have hjets := shiEndpoint_transition_jets D hvc.1 hvc.2 (hc (label j)) (hi (label j))
    hy hnew (shiPathTime N k.val) (shiPathVertexFrame P k) (P j (shiPathTime N k.val)) hP
  refine ⟨hP, hjets.1, ?_, hjets.2.2.1, ?_⟩
  · exact hjets.2.1.trans (congrArg (c (label j)) hInv)
  · simpa +instances only [Function.comp_apply, hInv] using! hjets.2.2.2.1

private theorem path_raw_quadratic (D : LeviCivitaData g)
    (c : OpenPartialHomeomorph M E) (s : ℝ) (x : E) (P : End) (z : E) :
    quadraticPathJet x (s • P)
      (-(shiChartChristoffel D c x).bilinearComp (s • P) (s • P)) z =
        shiRawCoordinateVariation D c s x P z := by
  simp only [quadraticPathJet, shiRawCoordinateVariation, neg_apply,
    ContinuousLinearMap.bilinearComp_apply, smul_apply, smul_neg, sub_eq_add_neg]

set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
theorem shiPathJoinedVariation_eq_position (D : LeviCivitaData g)
    (hN : 0 < N) (c : Fin m → OpenPartialHomeomorph M E)
    (cstar : OpenPartialHomeomorph M E) (label : Fin N → Fin m)
    (γ : ℝ → M) (P : Fin N → ℝ → End)
    (hinside : ∀ j : Fin N, MapsTo γ
      (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) (c (label j)).source)
    (hq : γ 1 ∈ cstar.source) (j : Fin N)
    (hPL : P j (shiPathTime N j.val) =
      (fderiv ℝ ((c (label j)) ∘ (shiPathVertexChart c cstar label j.castSucc).symm)
        (shiPathVertexCoordinate c cstar label γ j.castSucc)).comp
        (shiPathVertexFrame P j.castSucc))
    (hPR : P j (shiPathTime N (j.val + 1)) =
      (fderiv ℝ ((c (label j)) ∘ (shiPathVertexChart c cstar label j.succ).symm)
        (shiPathVertexCoordinate c cstar label γ j.succ)).comp
        (shiPathVertexFrame P j.succ)) (t : ℝ) (z : E) :
    shiPathJoinedVariation D c cstar label γ P j t z =
      shiJoinedPosition D (c (label j)) (shiPathVertexChart c cstar label j.castSucc)
        (shiPathVertexChart c cstar label j.succ)
        (shiPathTime N j.val) (shiPathTime N (j.val + 1))
        (shiPathTuple c cstar label γ P j t) z := by
  have hInv (k : Fin (N + 1)) : (shiPathVertexChart c cstar label k).symm
      (shiPathVertexCoordinate c cstar label γ k) = γ (shiPathTime N k.val) :=
    (shiPathVertexChart c cstar label k).left_inv
      (shiPath_vertex_source hN c cstar label γ hinside hq k)
  simp only [shiPathJoinedVariation, joinedCoordinateVariation, path_raw_quadratic,
    shiJoinedPosition, shiJoinedDiscrepancy, shiJoinedRawEndpoint, shiJoinedTransition,
    shiPathTuple, joinedTime, joinedX, joinedP, joinedYL, joinedQL, joinedYR, joinedQR,
    shiPathEndpoint, shiPathVertexMap, Function.comp_apply, Fin.val_castSucc,
    Fin.val_succ, hInv, ← hPL, ← hPR]

theorem shiPathJoinedVariation_endpoints (D : LeviCivitaData g)
    (hN : 0 < N) (c : Fin m → OpenPartialHomeomorph M E)
    (cstar : OpenPartialHomeomorph M E) (label : Fin N → Fin m)
    (γ : ℝ → M) (P : Fin N → ℝ → End) (j : Fin N) :
    shiPathJoinedVariation D c cstar label γ P j (shiPathTime N j.val) =
        shiPathEndpoint D c cstar label γ P j j.castSucc ∧
      shiPathJoinedVariation D c cstar label γ P j (shiPathTime N (j.val + 1)) =
        shiPathEndpoint D c cstar label γ P j j.succ := by
  have hba : shiPathTime N (j.val + 1) - shiPathTime N j.val ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (shiPathTime_step hN j.val))
  constructor <;> funext z
  · simp only [shiPathJoinedVariation, joinedCoordinateVariation, sub_self,
      div_self hba, one_smul, zero_div, zero_smul]
    abel
  · simp only [shiPathJoinedVariation, joinedCoordinateVariation, sub_self,
      div_self hba, one_smul, zero_div, zero_smul]
    abel

set_option backward.isDefEq.respectTransparency false in
theorem shiPathManifoldSegment_endpoints (D : LeviCivitaData g)
    (hN : 0 < N) (c : Fin m → OpenPartialHomeomorph M E)
    (cstar : OpenPartialHomeomorph M E) (label : Fin N → Fin m)
    (γ : ℝ → M) (P : Fin N → ℝ → End) (j : Fin N) (z : E)
    (hdom : (shiPathTuple c cstar label γ P j (shiPathTime N j.val), z) ∈
      shiJoinedDomain D (c (label j)) (shiPathVertexChart c cstar label j.castSucc)
        (shiPathVertexChart c cstar label j.succ)
        (shiPathTime N j.val) (shiPathTime N (j.val + 1))) :
    shiPathManifoldSegment D c cstar label γ P j z (shiPathTime N j.val) =
        shiPathVertexMap D c cstar label γ P j.castSucc z ∧
      shiPathManifoldSegment D c cstar label γ P j z (shiPathTime N (j.val + 1)) =
        shiPathVertexMap D c cstar label γ P j.succ z := by
  have he := shiPathJoinedVariation_endpoints D hN c cstar label γ P j
  constructor
  · unfold shiPathManifoldSegment
    rw [he.1]
    exact (c (label j)).left_inv hdom.2.1.2
  · unfold shiPathManifoldSegment
    rw [he.2]
    exact (c (label j)).left_inv hdom.2.2.1.2

theorem shiPathManifoldSegment_join (D : LeviCivitaData g)
    (hN : 0 < N) (c : Fin m → OpenPartialHomeomorph M E)
    (cstar : OpenPartialHomeomorph M E) (label : Fin N → Fin m)
    (γ : ℝ → M) (P : Fin N → ℝ → End) (j k : Fin N) (hjk : k.val = j.val + 1) (z : E)
    (hdom : ∀ i : Fin N, (shiPathTuple c cstar label γ P i (shiPathTime N i.val), z) ∈
      shiJoinedDomain D (c (label i)) (shiPathVertexChart c cstar label i.castSucc)
        (shiPathVertexChart c cstar label i.succ)
        (shiPathTime N i.val) (shiPathTime N (i.val + 1))) :
    shiPathManifoldSegment D c cstar label γ P j z (shiPathTime N (j.val + 1)) =
      shiPathManifoldSegment D c cstar label γ P k z (shiPathTime N k.val) := by
  have hv : j.succ = k.castSucc := Fin.ext hjk.symm
  rw [(shiPathManifoldSegment_endpoints D hN c cstar label γ P j z (hdom j)).2,
    (shiPathManifoldSegment_endpoints D hN c cstar label γ P k z (hdom k)).1, hv]

set_option maxHeartbeats 1600000 in

set_option synthInstance.maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency false in
theorem shiPathJoinedVariation_contDiffOn [T2Space M] (D : LeviCivitaData g)
    (c : Fin m → OpenPartialHomeomorph M E) (cstar : OpenPartialHomeomorph M E)
    (label : Fin N → Fin m) (γ : ℝ → M) (P : Fin N → ℝ → End)
    (hc : ∀ i, ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ (c i) (c i).source)
    (hi : ∀ i, ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (c i).symm (c i).target)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ)
    (hinside : ∀ j : Fin N, MapsTo γ
      (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) (c (label j)).source)
    (hP : ∀ j, ContDiffOn ℝ 1 (P j)
      (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))))
    (j : Fin N) (z : E) :
    ContDiffOn ℝ 1 (fun t => shiPathJoinedVariation D c cstar label γ P j t z)
      (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) := by
  let a := shiPathTime N j.val
  let b := shiPathTime N (j.val + 1)
  let x : ℝ → E := (c (label j)) ∘ γ
  let A : ℝ → End := fun t => t • P j t
  let B : ℝ → E →L[ℝ] E →L[ℝ] E := fun t =>
    -(shiChartChristoffel D (c (label j)) (x t)).bilinearComp (A t) (A t)
  have h1 : (1 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hx : ContDiffOn ℝ 1 x (Icc a b) :=
    (((hc (label j)).of_le h1).comp hγ.contMDiffOn (hinside j)).contDiffOn
  have hAz : ContDiffOn ℝ 1 (fun t => A t z) (Icc a b) :=
    contDiffOn_id.smul ((hP j).clm_apply contDiffOn_const)
  have hG : ContDiffOn ℝ 1
      (fun t => shiChartChristoffel D (c (label j)) (x t)) (Icc a b) :=
    ((shiChartChristoffel_smooth D (hc (label j)) (hi (label j))).of_le h1).comp hx
      (fun t ht => (c (label j)).map_source (hinside j ht))
  have hraw : ContDiffOn ℝ 1 (fun t => quadraticPathJet (x t) (A t) (B t) z) (Icc a b) := by
    simpa only [quadraticPathJet, B, neg_apply, ContinuousLinearMap.bilinearComp_apply,
      smul_neg, sub_eq_add_neg] using
      (hx.add hAz).sub (((hG.clm_apply hAz).clm_apply hAz).const_smul (1 / 2 : ℝ))
  have hwl : ContDiff ℝ 1 (fun t : ℝ => (b - t) / (b - a)) :=
    (contDiff_const.sub contDiff_id).div_const (b - a)
  have hwr : ContDiff ℝ 1 (fun t : ℝ => (t - a) / (b - a)) :=
    (contDiff_id.sub contDiff_const).div_const (b - a)
  exact (hraw.add (hwl.contDiffOn.smul contDiffOn_const)).add
    (hwr.contDiffOn.smul contDiffOn_const)

theorem shiPathManifoldSegment_contMDiffOn [T2Space M] (D : LeviCivitaData g)
    (c : Fin m → OpenPartialHomeomorph M E) (cstar : OpenPartialHomeomorph M E)
    (label : Fin N → Fin m) (γ : ℝ → M) (P : Fin N → ℝ → End)
    (hc : ∀ i, ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ (c i) (c i).source)
    (hi : ∀ i, ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (c i).symm (c i).target)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ)
    (hinside : ∀ j : Fin N, MapsTo γ
      (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) (c (label j)).source)
    (hP : ∀ j, ContDiffOn ℝ 1 (P j)
      (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))))
    (j : Fin N) (z : E)
    (htarget : MapsTo (fun t => shiPathJoinedVariation D c cstar label γ P j t z)
      (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) (c (label j)).target) :
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 (shiPathManifoldSegment D c cstar label γ P j z)
      (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) := by
  have h1 : (1 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  exact ((hi (label j)).of_le h1).comp
    (shiPathJoinedVariation_contDiffOn D c cstar label γ P hc hi hγ hinside hP j z).contMDiffOn
    htarget

theorem shiNormalChart_christoffel_zero (D : LeviCivitaData g)
    (c : OpenPartialHomeomorph M E) (q : M) (hq : q ∈ c.source) (h0 : c q = 0)
    (hH : ∀ i a b, D.hessian (shiChartCoordinate c i) q a b = 0) :
    shiChartChristoffel D c 0 = 0 := by
  have hinv : c.symm 0 = q := by rw [← h0]; exact c.left_inv hq
  have hHz : ∀ i a b, D.hessian (shiChartCoordinate c i) (c.symm 0) a b = 0 := by
    intro i a b
    rw [hinv]
    exact hH i a b
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  simp only [shiChartChristoffel, sum_apply, smul_apply, hHz, neg_zero,
    zero_smul, zero_apply, Finset.sum_const_zero]

theorem shiPathVertexMap_initial (D : LeviCivitaData g)
    (hN : 0 < N) (c : Fin m → OpenPartialHomeomorph M E)
    (cstar : OpenPartialHomeomorph M E) (label : Fin N → Fin m)
    (γ : ℝ → M) (P : Fin N → ℝ → End)
    (hsrc : γ 0 ∈ (c (label ⟨0, hN⟩)).source) (z : E) :
    shiPathVertexMap D c cstar label γ P 0 z = γ 0 := by
  simpa [shiPathVertexMap, shiPathVertexChart, shiPathVertexLabel, shiPathExtendedChart,
    shiPathVertexCoordinate, shiPathVertexFrame, shiPathTime, shiRawCoordinateVariation, hN]
    using (c (label ⟨0, hN⟩)).left_inv hsrc

theorem shiPathVertexMap_terminal (D : LeviCivitaData g)
    (hN : 0 < N) (c : Fin m → OpenPartialHomeomorph M E)
    (cstar : OpenPartialHomeomorph M E) (label : Fin N → Fin m)
    (γ : ℝ → M) (P : Fin N → ℝ → End)
    (hq : γ 1 ∈ cstar.source) (h0 : cstar (γ 1) = 0)
    (hH : ∀ i a b, D.hessian (shiChartCoordinate cstar i) (γ 1) a b = 0) (z : E) :
    shiPathVertexMap D c cstar label γ P (Fin.last N) z = cstar.symm z := by
  have hG := shiNormalChart_christoffel_zero D cstar (γ 1) hq h0 hH
  simp [shiPathVertexMap, shiPathVertexChart, shiPathVertexLabel, shiPathExtendedChart,
    shiPathVertexCoordinate, shiPathVertexFrame, shiRawCoordinateVariation,
    shiPathTime_last hN, h0, hG]

set_option maxHeartbeats 2400000 in

set_option backward.isDefEq.respectTransparency false in
theorem shiPathTuple_density_regular [T2Space M] (D : LeviCivitaData g)
    (c : Fin m → OpenPartialHomeomorph M E) (cstar : OpenPartialHomeomorph M E)
    (label : Fin N → Fin m) (γ : ℝ → M) (P : Fin N → ℝ → End)
    (hc : ∀ i, ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ (c i) (c i).source)
    (hi : ∀ i, ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (c i).symm (c i).target)
    (hstar : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cstar cstar.source)
    (hstari : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cstar.symm cstar.target)
    (j : Fin N) (ρ : ℝ)
    (htuple : ContinuousOn (shiPathTuple c cstar label γ P j)
      (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))))
    (hbase : MapsTo (shiPathTuple c cstar label γ P j)
      (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1)))
      (shiJoinedBaseSet (c (label j)) (shiPathVertexChart c cstar label j.castSucc)
        (shiPathVertexChart c cstar label j.succ)))
    (hdom : ∀ z : E, ‖z‖ < ρ →
      MapsTo (fun t => (shiPathTuple c cstar label γ P j t, z))
        (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1)))
        (shiJoinedDomain D (c (label j)) (shiPathVertexChart c cstar label j.castSucc)
          (shiPathVertexChart c cstar label j.succ)
          (shiPathTime N j.val) (shiPathTime N (j.val + 1)))) :
    let e : ℝ → E → ℝ := fun t =>
      shiJoinedDensity g D (c (label j)) (shiPathVertexChart c cstar label j.castSucc)
        (shiPathVertexChart c cstar label j.succ)
        (shiPathTime N j.val) (shiPathTime N (j.val + 1)) (shiPathTuple c cstar label γ P j t)
    (∀ z, ‖z‖ < ρ → ContinuousOn (fun t => e t z)
      (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1)))) ∧
    ContinuousOn (fun t => fderiv ℝ (e t) 0)
      (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) ∧
    ContinuousOn (fun t => fderiv ℝ (fderiv ℝ (e t)) 0)
      (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) := by
  have hl := shiPathVertexChart_smooth c cstar label hc hi hstar hstari j.castSucc
  have hr := shiPathVertexChart_smooth c cstar label hc hi hstar hstari j.succ
  have hjets := shiJoinedDensity_jet_continuousOn D (hc (label j)) (hi (label j))
    hl.1 hl.2 hr.1 hr.2 (shiPathTime N j.val) (shiPathTime N (j.val + 1))
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hc' := (shiJoinedDensity_contDiffOn D (hc (label j)) (hi (label j))
      hl.1 hl.2 hr.1 hr.2 (shiPathTime N j.val) (shiPathTime N (j.val + 1))).continuousOn
    have hpair : ContinuousOn
        (fun t => (shiPathTuple c cstar label γ P j t, z))
        (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) :=
      htuple.prodMk continuousOn_const
    simpa +instances only [Function.comp_def] using! hc'.comp hpair (hdom z hz)
  · simpa +instances only [Function.comp_def] using! hjets.1.comp htuple hbase
  · simpa +instances only [Function.comp_def] using! hjets.2.comp htuple hbase

end PoincareConjecture.RicciFlowAnalysis
