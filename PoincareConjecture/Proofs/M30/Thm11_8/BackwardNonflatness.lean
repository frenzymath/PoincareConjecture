import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Nonflatness
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.SectionalBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M30

theorem scalarCurvature_positive_somewhere_of_locally_bounded_ancient
    {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 3 M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hbounded : ∀ a ≤ 0, ∃ K : ℝ, 0 ≤ K ∧
      ∀ t ∈ Icc a 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (hterminal : ∃ p : M, 0 < (F.connection 0).scalarCurvature p) :
    ∀ a ≤ 0, ∃ x : M, 0 < (F.connection a).scalarCurvature x := by
  classical
  intro a ha
  rcases lt_or_eq_of_le ha with ha | rfl
  · by_contra hinit
    push Not at hinit
    obtain ⟨K, hK, hbound⟩ := hbounded a ha.le
    obtain ⟨p, hp⟩ := hterminal
    have hRic (t : ℝ) (ht : t ≤ 0) (x : M) (v : TangentSpace (𝓡 3) x) :
        0 ≤ (F.connection t).ricci x v v :=
      ((F.connection t).ricci_bounds_of_nonnegative_curvatureOperator
        (hC.tensor_calculus 3 M (F.metric t) (F.connection t)) x (hoperator t ht x) v).1
    by_cases hc : IsCompact (univ : Set M)
    · let : CompactSpace M := ⟨hc⟩
      have hnonpos : ∀ x t, t ∈ Icc a 0 → (F.connection t).scalarCurvature x ≤ 0 := by
        apply Poincare.Parabolic.nonpos_of_deriv_le_mul_at_max
          (F := fun x t => (F.connection t).scalarCurvature x)
          (F' := fun x t => (F.connection t).laplacian (F.connection t).scalarCurvature x +
            2 * (F.connection t).ricciNormSq x) (K := 2 * ((3 : ℝ) ^ 2 * K))
        · exact (hC.scalar_regular 3 M (Iic 0) F).continuousOn.comp
            (f := fun z : M × ℝ => (z.2, z.1))
            (continuous_snd.prodMk continuous_fst).continuousOn
            (fun z hz => ⟨hz.2.2, mem_univ z.1⟩)
        · intro x t ht
          exact (hC.scalar_evolution 3 M (Iic 0) F t ht.2 x).mono
            (fun _ hs => hs.2)
        · intro x t ht hpositive hmax
          have hsmooth := Poincare.RicciFlow.Harnack.scalarCurvature_contMDiff_slice
            hC (Iic 0) F t ht.2
          have hlap := (F.connection t).laplacian_nonpos_of_isLocalMax hsmooth
            (Filter.Eventually.of_forall hmax)
          have hricci := (F.connection t).ricciNormSq_le_scalarCurvature_sq_of_ricci_nonneg
            (hC.tensor_calculus 3 M (F.metric t) (F.connection t)) x (hRic t ht.2 x)
          have hscalar : (F.connection t).scalarCurvature x ≤ (3 : ℝ) ^ 2 * K :=
            (le_abs_self _).trans
              (((F.connection t).abs_scalarCurvature_le_curvatureTensorNorm x).trans
                (mul_le_mul_of_nonneg_left (hbound t ⟨ht.1.le, ht.2⟩ x) (sq_nonneg _)))
          have hreaction := mul_le_mul_of_nonneg_right hscalar hpositive.le
          nlinarith
        · exact hinit
      exact hp.not_ge (hnonpos p 0 ⟨ha.le, le_rfl⟩)
    · let : NoncompactSpace M := ⟨hc⟩
      have hzero : (F.connection a).scalarCurvature p = 0 :=
        le_antisymm (hinit p) (Finset.sum_nonneg fun i _ => hRic a ha.le p _)
      have hpast (t : ℝ) (hta : t ≤ a) (x : M) :
          (F.connection t).curvatureTensorNorm x = 0 := by
        let b := t - 1
        let T := a - b
        have hT : 0 < T := by dsimp [T, b]; linarith
        have hshift : (fun s : ℝ => s + b) '' Icc 0 T ⊆ Iic 0 := by
          rintro _ ⟨s, hs, rfl⟩
          change s + b ≤ 0
          dsimp [T] at hs
          linarith [hs.2]
        have hne : (Icc 0 T).Nontrivial :=
          ⟨0, ⟨le_rfl, hT.le⟩, T, ⟨hT.le, le_rfl⟩, hT.ne⟩
        let G := F.translate b hshift ordConnected_Icc hne
        have hsec : ∀ s ∈ Icc 0 T, (G.connection s).NonnegativeSectionalCurvature := by
          intro s hs y v w
          exact (F.connection (s + b)).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
            y (hoperator (s + b) (by dsimp [T] at hs; linarith [hs.2]) y) v w
        have hterminalG : (G.connection T).scalarCurvature p = 0 := by
          change (F.connection (T + b)).scalarCurvature p = 0
          exact (congrArg (fun s => (F.connection s).scalarCurvature p = 0)
            (show T + b = a by dsimp [T]; ring)).mpr hzero
        have hflat := hC.scalar_zero_rigidity M T hT G hsec p hterminalG
        have htime : (1 : ℝ) ∈ Icc 0 T := by
          constructor
          · norm_num
          · dsimp [T, b]
            linarith
        have hx := hflat 1 htime x
        change (F.connection (1 + b)).curvatureTensorNorm x = 0 at hx
        exact (congrArg (fun s => (F.connection s).curvatureTensorNorm x = 0)
          (show 1 + b = t by dsimp [b]; ring)).mp hx
      have hglobal (t : ℝ) (ht : t ≤ 0) (x : M) :
          (F.connection t).curvatureTensorNorm x ≤ K := by
        by_cases hta : t ≤ a
        · rw [hpast t hta x]
          exact hK
        · exact hbound t ⟨(lt_of_not_ge hta).le, ht⟩ x
      exact hp.not_ge (F.scalarCurvature_terminal_nonpos_of_bounded_ancient_slice_nonpos
        hC hcomplete hoperator hK hglobal ha hinit p)
  · exact hterminal

end PoincareConjecture.M30
