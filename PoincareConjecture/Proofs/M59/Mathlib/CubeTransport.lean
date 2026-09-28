import PoincareConjecture.Proofs.M02.CubeBoundaryAdjustment
import PoincareConjecture.Proofs.M02.HomotopyMap

set_option autoImplicit false

open scoped Topology unitInterval

noncomputable section

namespace GenLoop

variable {N X Y : Type*} [Finite N] [TopologicalSpace X] [TopologicalSpace Y]
  {x y z : X}

structure HomotopyAlong (p : Path x y) (a : GenLoop N X x) (b : GenLoop N X y)
    extends a.val.Homotopy b.val where
  boundary_path : ∀ (t : I) (v : Cube.boundary N), toHomotopy (t, v) = p t

namespace HomotopyAlong

variable {p : Path x y} {q : Path y z}
  {a : GenLoop N X x} {b : GenLoop N X y} {c : GenLoop N X z}

def refl (a : GenLoop N X x) : HomotopyAlong (Path.refl x) a a where
  toHomotopy := ContinuousMap.Homotopy.refl a.val
  boundary_path _ v := GenLoop.boundary a v v.property

def symm (H : HomotopyAlong p a b) : HomotopyAlong p.symm b a where
  toHomotopy := H.toHomotopy.symm
  boundary_path _ v := H.boundary_path _ v

def trans (H : HomotopyAlong p a b) (G : HomotopyAlong q b c) :
    HomotopyAlong (p.trans q) a c where
  toHomotopy := H.toHomotopy.trans G.toHomotopy
  boundary_path t v := by
    rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split_ifs
    · exact H.boundary_path _ v
    · exact G.boundary_path _ v

def ofRel {a b : GenLoop N X x} (H : a.val.HomotopyRel b.val (Cube.boundary N)) :
    HomotopyAlong (Path.refl x) a b where
  toHomotopy := H.toHomotopy
  boundary_path t v := (H.eq_fst t v.property).trans (GenLoop.boundary a v v.property)

def toRel {a b : GenLoop N X x} (H : HomotopyAlong (Path.refl x) a b) :
    a.val.HomotopyRel b.val (Cube.boundary N) where
  toHomotopy := H.toHomotopy
  prop' t v hv := (H.boundary_path t ⟨v, hv⟩).trans (GenLoop.boundary a v hv).symm

theorem change_path (H : HomotopyAlong p a b) {q : Path x y}
    (P : p.Homotopic q) : Nonempty (HomotopyAlong q a b) := by
  obtain ⟨P⟩ := P
  let K : C(I × (I × Cube.boundary N), X) :=
    ⟨fun v => P (v.1, v.2.1),
      P.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))⟩
  obtain ⟨H', hH'⟩ :=
    PoincareConjecture.Proofs.M02.exists_cube_homotopy_of_boundary_homotopy
      a.val b.val H.toHomotopy K
      (fun t v => (P.apply_zero t).trans (H.boundary_path t v).symm)
      (fun s v => (P.source s).trans (GenLoop.boundary a v v.property).symm)
      (fun s v => (P.target s).trans (GenLoop.boundary b v v.property).symm)
  exact ⟨{
    toHomotopy := H'
    boundary_path := fun t v => (hH' t v).trans (P.apply_one t) }⟩

theorem endpoint_homotopic {c : GenLoop N X y}
    (H : HomotopyAlong p a b) (G : HomotopyAlong p a c) : Homotopic b c :=
  PoincareConjecture.Proofs.M02.cube_homotopicRel_of_homotopies_with_same_boundary
    a.val b.val c.val H.toHomotopy G.toHomotopy
    (fun t v => (H.boundary_path t v).trans (G.boundary_path t v).symm)

def map (H : HomotopyAlong p a b) (f : C(X, Y)) :
    HomotopyAlong (p.map f.continuous)
      (PoincareConjecture.Proofs.M02.mapGenLoop f rfl a)
      (PoincareConjecture.Proofs.M02.mapGenLoop f rfl b) where
  toHomotopy := (ContinuousMap.Homotopy.refl f).comp H.toHomotopy
  boundary_path t v := congrArg f (H.boundary_path t v)

def const (p : Path x y) :
    HomotopyAlong p (GenLoop.const : GenLoop N X x) GenLoop.const where
  toFun v := p v.1
  continuous_toFun := p.continuous.comp continuous_fst
  map_zero_left _ := p.source
  map_one_left _ := p.target
  boundary_path _ _ := rfl

end HomotopyAlong

theorem exists_homotopyAlong (p : Path x y) (a : GenLoop N X x) :
    ∃ b : GenLoop N X y, Nonempty (HomotopyAlong p a b) := by
  let h : C(I × Cube.boundary N, X) :=
    ⟨fun v => p v.1, p.continuous.comp continuous_fst⟩
  obtain ⟨F, hF0, hFB⟩ := PoincareConjecture.Proofs.M02.exists_cube_homotopy_extension
    a.val h (fun v => p.source.trans (GenLoop.boundary a v v.property).symm)
  let b : GenLoop N X y :=
    ⟨⟨fun v => F (1, v), F.continuous.comp (continuous_const.prodMk continuous_id)⟩,
      fun v hv => (hFB 1 ⟨v, hv⟩).trans p.target⟩
  exact ⟨b, ⟨{ toContinuousMap := F
               map_zero_left := hF0
               map_one_left := fun _ => rfl
               boundary_path := hFB }⟩⟩

def boundaryTransport (p : Path x y) (a : GenLoop N X x) : GenLoop N X y :=
  Classical.choose (exists_homotopyAlong p a)

def boundaryTransportHomotopy (p : Path x y) (a : GenLoop N X x) :
    HomotopyAlong p a (boundaryTransport p a) :=
  Classical.choice (Classical.choose_spec (exists_homotopyAlong p a))

theorem boundaryTransport_homotopic_of_homotopyAlong
    {p : Path x y} {a : GenLoop N X x} {b : GenLoop N X y}
    (H : HomotopyAlong p a b) : Homotopic (boundaryTransport p a) b :=
  (boundaryTransportHomotopy p a).endpoint_homotopic H

theorem boundaryTransport_refl (a : GenLoop N X x) :
    Homotopic (boundaryTransport (Path.refl x) a) a :=
  boundaryTransport_homotopic_of_homotopyAlong (HomotopyAlong.refl a)

theorem boundaryTransport_trans (p : Path x y) (q : Path y z) (a : GenLoop N X x) :
    Homotopic (boundaryTransport (p.trans q) a)
      (boundaryTransport q (boundaryTransport p a)) :=
  boundaryTransport_homotopic_of_homotopyAlong
    ((boundaryTransportHomotopy p a).trans
      (boundaryTransportHomotopy q (boundaryTransport p a)))

theorem boundaryTransport_symm (p : Path x y) (a : GenLoop N X x) :
    Homotopic (boundaryTransport p.symm (boundaryTransport p a)) a :=
  boundaryTransport_homotopic_of_homotopyAlong (boundaryTransportHomotopy p a).symm

theorem boundaryTransport_homotopic (p : Path x y) {a b : GenLoop N X x}
    (h : Homotopic a b) : Homotopic (boundaryTransport p a) (boundaryTransport p b) := by
  obtain ⟨H⟩ := h
  obtain ⟨G⟩ := ((HomotopyAlong.ofRel H).trans (boundaryTransportHomotopy p b)).change_path
    (Path.Homotopic.refl_trans p)
  exact boundaryTransport_homotopic_of_homotopyAlong G

theorem boundaryTransport_path_homotopic {p q : Path x y} (h : p.Homotopic q)
    (a : GenLoop N X x) : Homotopic (boundaryTransport p a) (boundaryTransport q a) := by
  obtain ⟨H⟩ := (boundaryTransportHomotopy p a).change_path h
  exact (boundaryTransport_homotopic_of_homotopyAlong H).symm

theorem boundaryTransport_const (p : Path x y) :
    Homotopic (boundaryTransport p (GenLoop.const : GenLoop N X x)) GenLoop.const :=
  boundaryTransport_homotopic_of_homotopyAlong (HomotopyAlong.const p)

theorem boundaryTransport_map (p : Path x y) (a : GenLoop N X x) (f : C(X, Y)) :
    Homotopic
      (boundaryTransport (p.map f.continuous) (PoincareConjecture.Proofs.M02.mapGenLoop f rfl a))
      (PoincareConjecture.Proofs.M02.mapGenLoop f rfl (boundaryTransport p a)) :=
  boundaryTransport_homotopic_of_homotopyAlong ((boundaryTransportHomotopy p a).map f)

end GenLoop
