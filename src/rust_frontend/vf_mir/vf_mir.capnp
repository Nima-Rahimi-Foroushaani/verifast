@0x810f32815ffa3aa2;
struct Option(T) {
    union {
        nothing @0: Void;
        something @1: T;
    }
}

struct Ty {

    struct Const {
        ty @0: Ty;
    }

    struct GenArg {
        struct GenArgKind {
            union {
                lifetime @0: Void;
                type @1: Ty;
                const @2: Void;
            }
        }
        kind @0: GenArgKind;
    }

    struct IntTy {
        union {
            iSize @0: Void;
            i32 @1: Void;
        }
    }

    struct UIntTy {
        union {
            uSize @0: Void;
            u8 @1: Void;
            u16 @2: Void;
            u32 @3: Void;
            u64 @4: Void;
            u128 @5: Void;
        }
    }

    struct AdtDefId {
        name @0: Text;
    }

    struct AdtDef {
        struct VariantDef {
            name @0: Text;
            discr @1: UInt64;
            fields @2: List(Ty);
        }
        id @0: AdtDefId;
        variants @1: List(VariantDef);
        #TODO @Nima: We will need AdtFlags. For now it is just struct
    }

    struct AdtTy {
        id @0: AdtDefId;
        substs @1: List(GenArg);
    }

    struct FnDefId {
        name @0: Text;
    }

    struct FnDefTy {
        id @0: FnDefId;
        substs @1: List(GenArg);
    }

    struct TyKind {
        union {
            bool @0: Void;
            int @1: IntTy;
            uInt @2: UIntTy;
            adt @3: AdtTy;
            rawPtr @4: Ty;
            fnDef @5: FnDefTy;
            tuple @6: List(GenArg);
        }
    }

    kind @0: TyKind;
}

struct Body {
    struct SourceInfo {}

    struct Annotation {
        raw @0: Text;
    }

    struct Contract {
        annotations @0: List(Annotation);
    }

    struct DefKind {
        union {
            fn @0: Void;
            assocFn @1: Void;
        }
    }

    struct Mutability {
        union {
            mut @0: Void;
            not @1: Void;
        }
    }

    struct LocalDeclId {
        name @0: Text;
    }

    struct LocalDecl {
        mutability @0: Mutability;
        id @1: LocalDeclId;
        ty @2: Ty;
    }

    struct BasicBlockId {
        name @0: Text;
    }

    struct BasicBlock {
        struct Place {
            struct PlaceElement {
                union {
                    deref @0: Void;
                    field @1: Text;
                }
            }

            local @0: LocalDeclId;
            projection @1: List(PlaceElement);
        }

        struct Constant {
            struct ConstantKind {
                union {
                    ty @0: Ty.Const;
                    val @1: Void;
                }
            }

            literal @0: ConstantKind;
        }

        struct Operand {
            union {
                copy @0: Place;
                move @1: Place;
                constant @2: Constant;
            }
        }

        struct RValue {
            struct AddressOfData {
                mutability @0: Mutability;
                place @1: Place;
            }

            union {
                # Either move or copy depending on operand type
                use @0: Operand;
                addressOf @1: AddressOfData;
            }
        }

        struct Statement {
            struct StatementKind {
                struct AssignData {
                    place @0: Place;
                    rvalue @1: RValue;
                }

                union {
                    assign @0: AssignData;
                    nop @1: Void;
                }
            }

            sourceInfo @0: SourceInfo;
            kind @1: StatementKind;
        }

        struct Terminator {
            struct TerminatorKind {
                struct SwitchIntData {
                    struct SwitchTargets {
                        targets @0: List(BasicBlockId);
                        otherwise @1: Option(BasicBlockId);
                    }

                    discr @0: Operand;
                    targets @1: SwitchTargets;
                }

                struct FnCallData {
                    func @0: Operand;
                }

                union {
                    goto @0: BasicBlockId;
                    switchInt @1: SwitchIntData;
                    resume @2: Void;
                    return @3: Void;
                    call @4: FnCallData;
                }
            }

            sourceInfo @0: SourceInfo;
            kind @1: TerminatorKind;
        }

        id @0: BasicBlockId;
        statements @1: List(Statement);
        terminator @2: Terminator;
    }

    defKind @0: DefKind;
    defPath @1: Text;
    contract @2: Contract;
    argCount @3: UInt32;
    localDecls @4: List(LocalDecl);
    basicBlocks @5: List(BasicBlock);
}

struct VfMir {
    bodies @0: List(Body);
}
#TODO @Nima: For Clarity write a struct fields on top and then inner type definitions