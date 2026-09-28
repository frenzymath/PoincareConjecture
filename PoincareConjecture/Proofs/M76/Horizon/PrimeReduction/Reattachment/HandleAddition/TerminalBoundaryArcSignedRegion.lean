import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcClosedRegion
import Mathlib.LinearAlgebra.FiniteDimensional.Basic



set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

theorem exists_linear_second_coordinate
    (m : (ℝ × ℝ) →L[ℝ] ℝ) (w : ℝ × ℝ) (hw : m w = 1) :
    ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ), ∀ z,(L z).2 = m z := by
  let a := m (1,0)
  let b := m (0,1)
  have hm (z : ℝ × ℝ) : m z = a*z.1+b*z.2 := by
    have hz : z = z.1 • (1,0) + z.2 • (0,1) := by ext <;> simp
    conv_lhs => rw [hz,map_add,map_smul,map_smul]
    change z.1*a+z.2*b = a*z.1+b*z.2
    ring
  let f : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
    { toFun := fun z => (b*z.1-a*z.2,m z)
      map_add' := by intro x y; ext <;> simp [map_add] <;> ring
      map_smul' := by intro r x; ext <;> simp [map_smul] <;> ring }
  have hpos : 0 < a*a+b*b := by
    have hw' := (hm w).symm.trans hw
    by_contra hh
    have ha : a = 0 := by nlinarith [sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a]
    simp [ha,hb] at hw'
  have hfi : Function.Injective f := by
    intro x y h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    change b*x.1-a*x.2=b*y.1-a*y.2 at h1
    change m x=m y at h2
    rw [hm,hm] at h2
    have hx : (a*a+b*b)*(x.1-y.1)=0 := by nlinarith [congrArg (a*·) h2,congrArg (b*·) h1]
    have hy : (a*a+b*b)*(x.2-y.2)=0 := by nlinarith [congrArg (b*·) h2,congrArg (a*·) h1]
    exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hpos.ne'))
      (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left hpos.ne'))
  exact ⟨(LinearEquiv.ofBijective f ⟨hfi,LinearMap.surjective_of_injective hfi⟩).toContinuousLinearEquiv,
    fun _ => rfl⟩

theorem isSimplyConnected_closure_of_convex_flat_frontier
    {X : Type*} [MetricSpace X] [PreconnectedSpace X]
    {O : Set X} (hO : IsOpen O) (hsc : IsSimplyConnected O)
    (hproper : closure O ≠ univ) (hcompact : IsCompact (frontier O))
    (hconn : IsConnected (frontier O))
    (hcharts : ∀ x ∈ frontier O, ∃ H : OpenPartialHomeomorph X (ℝ × ℝ),
      x ∈ H.source ∧ ∃ (m : (ℝ × ℝ) →L[ℝ] ℝ) (w : ℝ × ℝ),
        m w = 1 ∧ Convex ℝ H.target ∧
        ∀ y ∈ H.source,y ∈ frontier O ↔ m (H y) = 0) :
    frontier (closure O) = frontier O ∧ IsSimplyConnected (closure O) := by
  let : SimplyConnectedSpace O := hsc
  have hne : O.Nonempty := (isConnected_iff_connectedSpace.mpr inferInstance).nonempty
  have hfront := frontier_closure_eq_of_connected_flat_frontier hO hne hproper hconn (by
    intro x hx
    obtain ⟨H,hxH,m,w,hm,hcv,hf⟩ := hcharts x hx
    exact ⟨H,hxH,m,hcv,hf⟩)
  refine ⟨hfront,isSimplyConnected_closure_of_signed_frontier_charts hO hcompact hconn.nonempty
    hfront ?_ hsc⟩
  intro x
  obtain ⟨H,hxH,m,w,hm,hcv,hf⟩ := hcharts x x.property
  have hreg : closure (interior (closure O)) = closure O := by
    apply Subset.antisymm
    · exact closure_minimal interior_subset isClosed_closure
    · exact closure_mono (interior_mono subset_closure |>.trans' hO.interior_eq.symm.subset)
  have hsign := halfspace_of_convex_linear_frontier_chart isClosed_closure hreg
    (hfront.symm ▸ x.property) H hxH m hcv (by simpa only [hfront] using hf)
  have hsigned : ∃ (k : (ℝ × ℝ) →L[ℝ] ℝ) (v : ℝ × ℝ),k v = 1 ∧
      (∀ y ∈ H.source,y ∈ closure O ↔ 0 ≤ k (H y)) ∧
      ∀ y ∈ H.source,y ∈ frontier O ↔ k (H y) = 0 := by
    rcases hsign with hp | hn
    · exact ⟨m,w,hm,hp,hf⟩
    · refine ⟨-m,-w,by simpa using hm,?_,?_⟩
      · intro y hy; simpa using hn y hy
      · intro y hy; simpa using hf y hy
  obtain ⟨k,v,hkv,hside,hzero⟩ := hsigned
  obtain ⟨L,hL⟩ := exists_linear_second_coordinate k v hkv
  let T := H.trans L.toHomeomorph.toOpenPartialHomeomorph
  have hTs : T.source = H.source := by ext y; simp [T]
  have hval (y : X) : (T y).2 = k (H y) := hL _
  refine ⟨T,hTs.symm ▸ hxH,?_,?_⟩
  · intro y hy
    rw [hval]
    exact hside y (hTs.subset hy)
  · intro y hy
    have hyH := hTs.subset hy
    have hOeq : O = closure O \ frontier O := by rw [closure_sdiff_frontier,hO.interior_eq]
    rw [hval,mem_compl_iff,hOeq,mem_sdiff,hside y hyH,hzero y hyH]
    constructor
    · intro hh
      by_contra hn
      exact hh ⟨(lt_of_not_ge hn).le,(lt_of_not_ge hn).ne'⟩
    · rintro hh ⟨hge,hne⟩
      exact hne (le_antisymm hh hge)

end PoincareConjecture.M76
