(module
  (type (;0;) (func (param i32)))
  (type (;1;) (func (param i32) (result i32)))
  (type (;2;) (func (param i32 i32) (result i32)))
  (type (;3;) (func (param i32 i32 i32) (result i32)))
  (type (;4;) (func (param i32 i32 i64)))
  (type (;5;) (func))
  (import "runtime" "__release" (func (;0;) (type 0)))
  (import "runtime" "EjArrayBuilder#finalize" (func (;1;) (type 1)))
  (import "runtime" "EjBool#get:value" (func (;2;) (type 1)))
  (import "runtime" "EjObject#constructor" (func (;3;) (type 1)))
  (import "runtime" "alloc_bytes" (func (;4;) (type 1)))
  (import "runtime" "ejson_of_bytes" (func (;5;) (type 1)))
  (import "runtime" "ejson_to_bytes" (func (;6;) (type 1)))
  (import "runtime" "runtimeEither" (func (;7;) (type 1)))
  (import "runtime" "runtimeToLeft" (func (;8;) (type 1)))
  (import "runtime" "runtimeUnbrand" (func (;9;) (type 1)))
  (import "runtime" "EjArrayBuilder#constructor" (func (;10;) (type 2)))
  (import "runtime" "EjArrayBuilder#put" (func (;11;) (type 2)))
  (import "runtime" "opAddString" (func (;12;) (type 2)))
  (import "runtime" "runtimeRecConcat" (func (;13;) (type 2)))
  (import "runtime" "runtimeRecDot" (func (;14;) (type 2)))
  (import "runtime" "EjObject#set" (func (;15;) (type 3)))
  (import "runtime" "runtimeCast" (func (;16;) (type 3)))
  (import "runtime" "bytes_set_i64" (func (;17;) (type 4)))
  (func (;18;) (type 1) (param i32) (result i32)
    (local i32 i32 i32 i32 i32)
    local.get 0
    i32.load offset=4
    local.tee 5
    call 4
    local.set 2
    i32.const 0
    local.set 3
    local.get 0
    i32.const 8
    i32.add
    local.set 1
    loop  ;; label = @1
      local.get 5
      i32.const 0
      i32.gt_s
      if  ;; label = @2
        local.get 2
        local.get 3
        local.get 1
        i64.load
        call 17
        local.get 3
        i32.const 8
        i32.add
        local.set 3
        local.get 1
        i32.const 8
        i32.add
        local.set 1
        local.get 5
        i32.const 8
        i32.sub
        local.set 5
        br 1 (;@1;)
      end
    end
    local.get 2
    call 5
    local.set 4
    local.get 2
    call 0
    local.get 4)
  (func (;19;) (type 1) (param i32) (result i32)
    (local i32)
    local.get 0
    i32.load
    local.tee 1
    i32.eqz
    if  ;; label = @1
      local.get 0
      local.get 0
      call 18
      local.tee 1
      i32.store
    end
    local.get 1)
  (func (;20;) (type 1) (param i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32)
    local.get 0
    local.get 0
    call 5
    local.set 0
    call 0
    block (result i32)  ;; label = @1
      block (result i32)  ;; label = @2
        local.get 0
      end
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          i32.const 1984
          call 19
        end
      end
      call 14
    end
    local.set 2
    block (result i32)  ;; label = @1
      block (result i32)  ;; label = @2
        local.get 0
      end
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          i32.const 2008
          call 19
        end
      end
      call 14
    end
    local.set 3
    block (result i32)  ;; label = @1
      block (result i32)  ;; label = @2
        local.get 0
      end
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          i32.const 2032
          call 19
        end
      end
      call 14
    end
    local.set 4
    block (result i32)  ;; label = @1
      block (result i32)  ;; label = @2
        local.get 0
      end
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          i32.const 2056
          call 19
        end
      end
      call 14
    end
    local.set 5
    block (result i32)  ;; label = @1
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          block (result i32)  ;; label = @4
            i32.const 0
            call 19
          end
          block (result i32)  ;; label = @4
            block (result i32)  ;; label = @5
              i32.const 0
              i32.const 1
              call 10
              block (result i32)  ;; label = @6
                block (result i32)  ;; label = @7
                  i32.const 2080
                  call 19
                end
              end
              call 11
              call 1
            end
          end
          block (result i32)  ;; label = @4
            local.get 5
          end
          call 16
        end
      end
      call 7
    end
    call 2
    if  ;; label = @1
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          block (result i32)  ;; label = @4
            block (result i32)  ;; label = @5
              i32.const 0
              call 19
            end
            block (result i32)  ;; label = @5
              block (result i32)  ;; label = @6
                i32.const 0
                i32.const 1
                call 10
                block (result i32)  ;; label = @7
                  block (result i32)  ;; label = @8
                    i32.const 2080
                    call 19
                  end
                end
                call 11
                call 1
              end
            end
            block (result i32)  ;; label = @5
              local.get 5
            end
            call 16
          end
        end
        call 8
      end
      local.set 7
      block (result i32)  ;; label = @2
        i32.const 0
        call 3
        block (result i32)  ;; label = @3
          i32.const 2160
          call 19
        end
        block (result i32)  ;; label = @3
          block (result i32)  ;; label = @4
            i32.const 0
            call 3
            block (result i32)  ;; label = @5
              i32.const 2136
              call 19
            end
            block (result i32)  ;; label = @5
              local.get 7
            end
            call 15
          end
        end
        call 15
      end
      local.set 6
    else
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          block (result i32)  ;; label = @4
            block (result i32)  ;; label = @5
              i32.const 0
              call 19
            end
            block (result i32)  ;; label = @5
              block (result i32)  ;; label = @6
                i32.const 0
                i32.const 1
                call 10
                block (result i32)  ;; label = @7
                  block (result i32)  ;; label = @8
                    i32.const 2080
                    call 19
                  end
                end
                call 11
                call 1
              end
            end
            block (result i32)  ;; label = @5
              local.get 5
            end
            call 16
          end
        end
        call 8
      end
      local.set 7
      block (result i32)  ;; label = @2
        i32.const 0
        call 3
        block (result i32)  ;; label = @3
          i32.const 2160
          call 19
        end
        block (result i32)  ;; label = @3
          block (result i32)  ;; label = @4
            i32.const 0
            call 3
            block (result i32)  ;; label = @5
              i32.const 2136
              call 19
            end
            block (result i32)  ;; label = @5
              local.get 7
            end
            call 15
          end
        end
        call 15
      end
      local.set 6
    end
    block (result i32)  ;; label = @1
      block (result i32)  ;; label = @2
        local.get 6
      end
      call 7
    end
    call 2
    if  ;; label = @1
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          local.get 6
        end
        call 8
      end
      local.set 7
      local.get 7
      local.set 8
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          local.get 8
        end
        block (result i32)  ;; label = @3
          block (result i32)  ;; label = @4
            i32.const 2136
            call 19
          end
        end
        call 14
      end
      local.set 9
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          local.get 0
        end
        block (result i32)  ;; label = @3
          block (result i32)  ;; label = @4
            i32.const 2032
            call 19
          end
        end
        call 14
      end
      local.set 10
      local.get 2
      local.set 11
      local.get 3
      local.set 12
      local.get 9
      local.set 13
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          local.get 0
        end
        block (result i32)  ;; label = @3
          block (result i32)  ;; label = @4
            i32.const 1984
            call 19
          end
        end
        call 14
      end
      local.set 14
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          local.get 0
        end
        block (result i32)  ;; label = @3
          block (result i32)  ;; label = @4
            i32.const 2008
            call 19
          end
        end
        call 14
      end
      local.set 15
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          local.get 0
        end
        block (result i32)  ;; label = @3
          block (result i32)  ;; label = @4
            i32.const 2032
            call 19
          end
        end
        call 14
      end
      local.set 16
      block (result i32)  ;; label = @2
        i32.const 0
        call 3
        block (result i32)  ;; label = @3
          i32.const 2160
          call 19
        end
        block (result i32)  ;; label = @3
          block (result i32)  ;; label = @4
            block (result i32)  ;; label = @5
              block (result i32)  ;; label = @6
                block (result i32)  ;; label = @7
                  block (result i32)  ;; label = @8
                    i32.const 0
                    call 3
                    block (result i32)  ;; label = @9
                      i32.const 2416
                      call 19
                    end
                    block (result i32)  ;; label = @9
                      block (result i32)  ;; label = @10
                        i32.const 0
                        call 3
                        block (result i32)  ;; label = @11
                          i32.const 2368
                          call 19
                        end
                        block (result i32)  ;; label = @11
                          block (result i32)  ;; label = @12
                            i32.const 0
                            i32.const 1
                            call 10
                            block (result i32)  ;; label = @13
                              block (result i32)  ;; label = @14
                                i32.const 2184
                                call 19
                              end
                            end
                            call 11
                            call 1
                          end
                        end
                        call 15
                        block (result i32)  ;; label = @11
                          i32.const 2392
                          call 19
                        end
                        block (result i32)  ;; label = @11
                          block (result i32)  ;; label = @12
                            i32.const 0
                            call 3
                            block (result i32)  ;; label = @13
                              i32.const 2344
                              call 19
                            end
                            block (result i32)  ;; label = @13
                              block (result i32)  ;; label = @14
                                block (result i32)  ;; label = @15
                                  block (result i32)  ;; label = @16
                                    block (result i32)  ;; label = @17
                                      block (result i32)  ;; label = @18
                                        block (result i32)  ;; label = @19
                                          block (result i32)  ;; label = @20
                                            block (result i32)  ;; label = @21
                                              block (result i32)  ;; label = @22
                                                i32.const 2240
                                                call 19
                                              end
                                            end
                                            block (result i32)  ;; label = @21
                                              block (result i32)  ;; label = @22
                                                block (result i32)  ;; label = @23
                                                  block (result i32)  ;; label = @24
                                                    block (result i32)  ;; label = @25
                                                      block (result i32)  ;; label = @26
                                                        block (result i32)  ;; label = @27
                                                          local.get 0
                                                        end
                                                        block (result i32)  ;; label = @27
                                                          block (result i32)  ;; label = @28
                                                            i32.const 2032
                                                            call 19
                                                          end
                                                        end
                                                        call 14
                                                      end
                                                    end
                                                    call 9
                                                  end
                                                end
                                                block (result i32)  ;; label = @23
                                                  block (result i32)  ;; label = @24
                                                    i32.const 2264
                                                    call 19
                                                  end
                                                end
                                                call 14
                                              end
                                            end
                                            call 12
                                          end
                                        end
                                        block (result i32)  ;; label = @19
                                          block (result i32)  ;; label = @20
                                            i32.const 2288
                                            call 19
                                          end
                                        end
                                        call 12
                                      end
                                    end
                                    block (result i32)  ;; label = @17
                                      block (result i32)  ;; label = @18
                                        block (result i32)  ;; label = @19
                                          block (result i32)  ;; label = @20
                                            block (result i32)  ;; label = @21
                                              block (result i32)  ;; label = @22
                                                block (result i32)  ;; label = @23
                                                  local.get 0
                                                end
                                                block (result i32)  ;; label = @23
                                                  block (result i32)  ;; label = @24
                                                    i32.const 2056
                                                    call 19
                                                  end
                                                end
                                                call 14
                                              end
                                            end
                                            call 9
                                          end
                                        end
                                        block (result i32)  ;; label = @19
                                          block (result i32)  ;; label = @20
                                            i32.const 2304
                                            call 19
                                          end
                                        end
                                        call 14
                                      end
                                    end
                                    call 12
                                  end
                                end
                                block (result i32)  ;; label = @15
                                  block (result i32)  ;; label = @16
                                    i32.const 2328
                                    call 19
                                  end
                                end
                                call 12
                              end
                            end
                            call 15
                          end
                        end
                        call 15
                      end
                    end
                    call 15
                  end
                end
                block (result i32)  ;; label = @7
                  block (result i32)  ;; label = @8
                    i32.const 0
                    call 3
                    block (result i32)  ;; label = @9
                      i32.const 1984
                      call 19
                    end
                    block (result i32)  ;; label = @9
                      local.get 14
                    end
                    call 15
                  end
                end
                call 13
              end
            end
            block (result i32)  ;; label = @5
              block (result i32)  ;; label = @6
                i32.const 0
                call 3
                block (result i32)  ;; label = @7
                  i32.const 2008
                  call 19
                end
                block (result i32)  ;; label = @7
                  local.get 15
                end
                call 15
              end
            end
            call 13
          end
        end
        call 15
      end
      local.set 1
    else
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          local.get 6
        end
        call 8
      end
      local.set 7
      local.get 7
      local.set 8
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          local.get 8
        end
        block (result i32)  ;; label = @3
          block (result i32)  ;; label = @4
            i32.const 2136
            call 19
          end
        end
        call 14
      end
      local.set 9
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          local.get 0
        end
        block (result i32)  ;; label = @3
          block (result i32)  ;; label = @4
            i32.const 2032
            call 19
          end
        end
        call 14
      end
      local.set 10
      local.get 2
      local.set 11
      local.get 3
      local.set 12
      local.get 9
      local.set 13
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          local.get 0
        end
        block (result i32)  ;; label = @3
          block (result i32)  ;; label = @4
            i32.const 1984
            call 19
          end
        end
        call 14
      end
      local.set 14
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          local.get 0
        end
        block (result i32)  ;; label = @3
          block (result i32)  ;; label = @4
            i32.const 2008
            call 19
          end
        end
        call 14
      end
      local.set 15
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          local.get 0
        end
        block (result i32)  ;; label = @3
          block (result i32)  ;; label = @4
            i32.const 2032
            call 19
          end
        end
        call 14
      end
      local.set 16
      block (result i32)  ;; label = @2
        i32.const 0
        call 3
        block (result i32)  ;; label = @3
          i32.const 2160
          call 19
        end
        block (result i32)  ;; label = @3
          block (result i32)  ;; label = @4
            block (result i32)  ;; label = @5
              block (result i32)  ;; label = @6
                block (result i32)  ;; label = @7
                  block (result i32)  ;; label = @8
                    i32.const 0
                    call 3
                    block (result i32)  ;; label = @9
                      i32.const 2416
                      call 19
                    end
                    block (result i32)  ;; label = @9
                      block (result i32)  ;; label = @10
                        i32.const 0
                        call 3
                        block (result i32)  ;; label = @11
                          i32.const 2368
                          call 19
                        end
                        block (result i32)  ;; label = @11
                          block (result i32)  ;; label = @12
                            i32.const 0
                            i32.const 1
                            call 10
                            block (result i32)  ;; label = @13
                              block (result i32)  ;; label = @14
                                i32.const 2184
                                call 19
                              end
                            end
                            call 11
                            call 1
                          end
                        end
                        call 15
                        block (result i32)  ;; label = @11
                          i32.const 2392
                          call 19
                        end
                        block (result i32)  ;; label = @11
                          block (result i32)  ;; label = @12
                            i32.const 0
                            call 3
                            block (result i32)  ;; label = @13
                              i32.const 2344
                              call 19
                            end
                            block (result i32)  ;; label = @13
                              block (result i32)  ;; label = @14
                                block (result i32)  ;; label = @15
                                  block (result i32)  ;; label = @16
                                    block (result i32)  ;; label = @17
                                      block (result i32)  ;; label = @18
                                        block (result i32)  ;; label = @19
                                          block (result i32)  ;; label = @20
                                            block (result i32)  ;; label = @21
                                              block (result i32)  ;; label = @22
                                                i32.const 2240
                                                call 19
                                              end
                                            end
                                            block (result i32)  ;; label = @21
                                              block (result i32)  ;; label = @22
                                                block (result i32)  ;; label = @23
                                                  block (result i32)  ;; label = @24
                                                    block (result i32)  ;; label = @25
                                                      block (result i32)  ;; label = @26
                                                        block (result i32)  ;; label = @27
                                                          local.get 0
                                                        end
                                                        block (result i32)  ;; label = @27
                                                          block (result i32)  ;; label = @28
                                                            i32.const 2032
                                                            call 19
                                                          end
                                                        end
                                                        call 14
                                                      end
                                                    end
                                                    call 9
                                                  end
                                                end
                                                block (result i32)  ;; label = @23
                                                  block (result i32)  ;; label = @24
                                                    i32.const 2264
                                                    call 19
                                                  end
                                                end
                                                call 14
                                              end
                                            end
                                            call 12
                                          end
                                        end
                                        block (result i32)  ;; label = @19
                                          block (result i32)  ;; label = @20
                                            i32.const 2288
                                            call 19
                                          end
                                        end
                                        call 12
                                      end
                                    end
                                    block (result i32)  ;; label = @17
                                      block (result i32)  ;; label = @18
                                        block (result i32)  ;; label = @19
                                          block (result i32)  ;; label = @20
                                            block (result i32)  ;; label = @21
                                              block (result i32)  ;; label = @22
                                                block (result i32)  ;; label = @23
                                                  local.get 0
                                                end
                                                block (result i32)  ;; label = @23
                                                  block (result i32)  ;; label = @24
                                                    i32.const 2056
                                                    call 19
                                                  end
                                                end
                                                call 14
                                              end
                                            end
                                            call 9
                                          end
                                        end
                                        block (result i32)  ;; label = @19
                                          block (result i32)  ;; label = @20
                                            i32.const 2304
                                            call 19
                                          end
                                        end
                                        call 14
                                      end
                                    end
                                    call 12
                                  end
                                end
                                block (result i32)  ;; label = @15
                                  block (result i32)  ;; label = @16
                                    i32.const 2328
                                    call 19
                                  end
                                end
                                call 12
                              end
                            end
                            call 15
                          end
                        end
                        call 15
                      end
                    end
                    call 15
                  end
                end
                block (result i32)  ;; label = @7
                  block (result i32)  ;; label = @8
                    i32.const 0
                    call 3
                    block (result i32)  ;; label = @9
                      i32.const 1984
                      call 19
                    end
                    block (result i32)  ;; label = @9
                      local.get 14
                    end
                    call 15
                  end
                end
                call 13
              end
            end
            block (result i32)  ;; label = @5
              block (result i32)  ;; label = @6
                i32.const 0
                call 3
                block (result i32)  ;; label = @7
                  i32.const 2008
                  call 19
                end
                block (result i32)  ;; label = @7
                  local.get 15
                end
                call 15
              end
            end
            call 13
          end
        end
        call 15
      end
      local.set 1
    end
    local.get 1
    call 6)
  (func (;21;) (type 1) (param i32) (result i32)
    (local i32 i32 i32 i32 i32)
    local.get 0
    local.get 0
    call 5
    local.set 0
    call 0
    block (result i32)  ;; label = @1
      block (result i32)  ;; label = @2
        local.get 0
      end
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          i32.const 1984
          call 19
        end
      end
      call 14
    end
    local.set 2
    block (result i32)  ;; label = @1
      block (result i32)  ;; label = @2
        local.get 0
      end
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          i32.const 2008
          call 19
        end
      end
      call 14
    end
    local.set 3
    block (result i32)  ;; label = @1
      block (result i32)  ;; label = @2
        local.get 0
      end
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          i32.const 2032
          call 19
        end
      end
      call 14
    end
    local.set 4
    block (result i32)  ;; label = @1
      i32.const 0
      call 3
      block (result i32)  ;; label = @2
        i32.const 2368
        call 19
      end
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          i32.const 0
          i32.const 1
          call 10
          block (result i32)  ;; label = @4
            block (result i32)  ;; label = @5
              i32.const 2440
              call 19
            end
          end
          call 11
          call 1
        end
      end
      call 15
      block (result i32)  ;; label = @2
        i32.const 2392
        call 19
      end
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          i32.const 0
          call 3
          block (result i32)  ;; label = @4
            i32.const 2584
            call 19
          end
          block (result i32)  ;; label = @4
            block (result i32)  ;; label = @5
              i32.const 2512
              call 19
            end
          end
          call 15
        end
      end
      call 15
    end
    local.set 5
    block (result i32)  ;; label = @1
      i32.const 0
      call 3
      block (result i32)  ;; label = @2
        i32.const 2160
        call 19
      end
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          block (result i32)  ;; label = @4
            block (result i32)  ;; label = @5
              block (result i32)  ;; label = @6
                block (result i32)  ;; label = @7
                  i32.const 0
                  call 3
                  block (result i32)  ;; label = @8
                    i32.const 2416
                    call 19
                  end
                  block (result i32)  ;; label = @8
                    block (result i32)  ;; label = @9
                      i32.const 2608
                      call 19
                    end
                  end
                  call 15
                end
              end
              block (result i32)  ;; label = @6
                block (result i32)  ;; label = @7
                  i32.const 0
                  call 3
                  block (result i32)  ;; label = @8
                    i32.const 1984
                    call 19
                  end
                  block (result i32)  ;; label = @8
                    local.get 5
                  end
                  call 15
                end
              end
              call 13
            end
          end
          block (result i32)  ;; label = @4
            block (result i32)  ;; label = @5
              i32.const 0
              call 3
              block (result i32)  ;; label = @6
                i32.const 2008
                call 19
              end
              block (result i32)  ;; label = @6
                local.get 3
              end
              call 15
            end
          end
          call 13
        end
      end
      call 15
    end
    local.set 1
    local.get 1
    call 6)
  (func (;22;) (type 1) (param i32) (result i32)
    (local i32 i32 i32 i32)
    local.get 0
    local.get 0
    call 5
    local.set 0
    call 0
    block (result i32)  ;; label = @1
      block (result i32)  ;; label = @2
        local.get 0
      end
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          i32.const 1984
          call 19
        end
      end
      call 14
    end
    local.set 2
    block (result i32)  ;; label = @1
      block (result i32)  ;; label = @2
        local.get 0
      end
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          i32.const 2008
          call 19
        end
      end
      call 14
    end
    local.set 3
    block (result i32)  ;; label = @1
      block (result i32)  ;; label = @2
        local.get 0
      end
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          i32.const 2032
          call 19
        end
      end
      call 14
    end
    local.set 4
    block (result i32)  ;; label = @1
      i32.const 0
      call 3
      block (result i32)  ;; label = @2
        i32.const 2160
        call 19
      end
      block (result i32)  ;; label = @2
        block (result i32)  ;; label = @3
          block (result i32)  ;; label = @4
            block (result i32)  ;; label = @5
              block (result i32)  ;; label = @6
                block (result i32)  ;; label = @7
                  i32.const 0
                  call 3
                  block (result i32)  ;; label = @8
                    i32.const 2416
                    call 19
                  end
                  block (result i32)  ;; label = @8
                    block (result i32)  ;; label = @9
                      i32.const 0
                      call 3
                      block (result i32)  ;; label = @10
                        i32.const 2368
                        call 19
                      end
                      block (result i32)  ;; label = @10
                        block (result i32)  ;; label = @11
                          i32.const 0
                          i32.const 1
                          call 10
                          block (result i32)  ;; label = @12
                            block (result i32)  ;; label = @13
                              i32.const 2184
                              call 19
                            end
                          end
                          call 11
                          call 1
                        end
                      end
                      call 15
                      block (result i32)  ;; label = @10
                        i32.const 2392
                        call 19
                      end
                      block (result i32)  ;; label = @10
                        block (result i32)  ;; label = @11
                          i32.const 0
                          call 3
                          block (result i32)  ;; label = @12
                            i32.const 2344
                            call 19
                          end
                          block (result i32)  ;; label = @12
                            block (result i32)  ;; label = @13
                              block (result i32)  ;; label = @14
                                block (result i32)  ;; label = @15
                                  block (result i32)  ;; label = @16
                                    block (result i32)  ;; label = @17
                                      block (result i32)  ;; label = @18
                                        block (result i32)  ;; label = @19
                                          block (result i32)  ;; label = @20
                                            block (result i32)  ;; label = @21
                                              i32.const 2240
                                              call 19
                                            end
                                          end
                                          block (result i32)  ;; label = @20
                                            block (result i32)  ;; label = @21
                                              block (result i32)  ;; label = @22
                                                block (result i32)  ;; label = @23
                                                  block (result i32)  ;; label = @24
                                                    block (result i32)  ;; label = @25
                                                      block (result i32)  ;; label = @26
                                                        local.get 0
                                                      end
                                                      block (result i32)  ;; label = @26
                                                        block (result i32)  ;; label = @27
                                                          i32.const 2032
                                                          call 19
                                                        end
                                                      end
                                                      call 14
                                                    end
                                                  end
                                                  call 9
                                                end
                                              end
                                              block (result i32)  ;; label = @22
                                                block (result i32)  ;; label = @23
                                                  i32.const 2264
                                                  call 19
                                                end
                                              end
                                              call 14
                                            end
                                          end
                                          call 12
                                        end
                                      end
                                      block (result i32)  ;; label = @18
                                        block (result i32)  ;; label = @19
                                          i32.const 2288
                                          call 19
                                        end
                                      end
                                      call 12
                                    end
                                  end
                                  block (result i32)  ;; label = @16
                                    block (result i32)  ;; label = @17
                                      block (result i32)  ;; label = @18
                                        block (result i32)  ;; label = @19
                                          block (result i32)  ;; label = @20
                                            block (result i32)  ;; label = @21
                                              block (result i32)  ;; label = @22
                                                local.get 0
                                              end
                                              block (result i32)  ;; label = @22
                                                block (result i32)  ;; label = @23
                                                  i32.const 2056
                                                  call 19
                                                end
                                              end
                                              call 14
                                            end
                                          end
                                          call 9
                                        end
                                      end
                                      block (result i32)  ;; label = @18
                                        block (result i32)  ;; label = @19
                                          i32.const 2304
                                          call 19
                                        end
                                      end
                                      call 14
                                    end
                                  end
                                  call 12
                                end
                              end
                              block (result i32)  ;; label = @14
                                block (result i32)  ;; label = @15
                                  i32.const 2328
                                  call 19
                                end
                              end
                              call 12
                            end
                          end
                          call 15
                        end
                      end
                      call 15
                    end
                  end
                  call 15
                end
              end
              block (result i32)  ;; label = @6
                block (result i32)  ;; label = @7
                  i32.const 0
                  call 3
                  block (result i32)  ;; label = @8
                    i32.const 1984
                    call 19
                  end
                  block (result i32)  ;; label = @8
                    local.get 2
                  end
                  call 15
                end
              end
              call 13
            end
          end
          block (result i32)  ;; label = @4
            block (result i32)  ;; label = @5
              i32.const 0
              call 3
              block (result i32)  ;; label = @6
                i32.const 2008
                call 19
              end
              block (result i32)  ;; label = @6
                local.get 3
              end
              call 15
            end
          end
          call 13
        end
      end
      call 15
    end
    local.set 1
    local.get 1
    call 6)
  (memory (;0;) 1)
  (export "main" (func 20))
  (export "init" (func 21))
  (export "helloworld" (func 22))
  (data (;0;) (i32.const 0) "\00\00\00\00\b6\07\00\00\06\16\00\00\00\06\02\00\00\00\05%\00\00\00org.accordproject.helloworld.Response\05\22\00\00\00org.accordproject.base.Transaction\06\02\00\00\00\05$\00\00\00org.accordproject.helloworld.Request\05\22\00\00\00org.accordproject.base.Transaction\06\02\00\00\00\05!\00\00\00org.accordproject.time.PeriodUnit\05\1b\00\00\00org.accordproject.base.Enum\06\02\00\00\00\05#\00\00\00org.accordproject.time.TemporalUnit\05\1b\00\00\00org.accordproject.base.Enum\06\02\00\00\00\05\1a\00\00\00org.accordproject.time.Day\05\1b\00\00\00org.accordproject.base.Enum\06\02\00\00\00\05\1c\00\00\00org.accordproject.time.Month\05\1b\00\00\00org.accordproject.base.Enum\06\02\00\00\00\05/\00\00\00org.accordproject.ergo.stdlib.ErgoErrorResponse\05.\00\00\00org.accordproject.cicero.runtime.ErrorResponse\06\02\00\00\00\05/\00\00\00org.accordproject.ergo.stdlib.ErgoErrorResponse\05\22\00\00\00org.accordproject.base.Transaction\06\02\00\00\00\057\00\00\00org.accordproject.cicero.runtime.NotificationObligation\05+\00\00\00org.accordproject.cicero.runtime.Obligation\06\02\00\00\00\057\00\00\00org.accordproject.cicero.runtime.NotificationObligation\05\1c\00\00\00org.accordproject.base.Event\06\02\00\00\00\052\00\00\00org.accordproject.cicero.runtime.PaymentObligation\05+\00\00\00org.accordproject.cicero.runtime.Obligation\06\02\00\00\00\052\00\00\00org.accordproject.cicero.runtime.PaymentObligation\05\1c\00\00\00org.accordproject.base.Event\06\02\00\00\00\05+\00\00\00org.accordproject.cicero.runtime.Obligation\05\1c\00\00\00org.accordproject.base.Event\06\02\00\00\00\05.\00\00\00org.accordproject.cicero.runtime.ErrorResponse\05\22\00\00\00org.accordproject.base.Transaction\06\02\00\00\00\05)\00\00\00org.accordproject.cicero.runtime.Response\05\22\00\00\00org.accordproject.base.Transaction\06\02\00\00\00\05(\00\00\00org.accordproject.cicero.runtime.Request\05\22\00\00\00org.accordproject.base.Transaction\06\02\00\00\00\05$\00\00\00org.accordproject.money.CurrencyCode\05\1b\00\00\00org.accordproject.base.Enum\06\02\00\00\00\05*\00\00\00org.accordproject.money.CryptoCurrencyCode\05\1b\00\00\00org.accordproject.base.Enum\06\02\00\00\00\05.\00\00\00org.accordproject.cicero.contract.AccordClause\05\1c\00\00\00org.accordproject.base.Asset\06\02\00\00\00\050\00\00\00org.accordproject.cicero.contract.AccordContract\05\1c\00\00\00org.accordproject.base.Asset\06\02\00\00\00\05-\00\00\00org.accordproject.cicero.contract.AccordParty\05\22\00\00\00org.accordproject.base.Participant\06\02\00\00\00\055\00\00\00org.accordproject.cicero.contract.AccordContractState\05\1c\00\00\00org.accordproject.base.Asset\00\00")
  (data (;1;) (i32.const 1984) "\00\00\00\00\0c\00\00\00\05\07\00\00\00__state\00\00\00\00")
  (data (;2;) (i32.const 2008) "\00\00\00\00\0b\00\00\00\05\06\00\00\00__emit\00\00\00\00\00")
  (data (;3;) (i32.const 2032) "\00\00\00\00\0f\00\00\00\05\0a\00\00\00__contract\00")
  (data (;4;) (i32.const 2056) "\00\00\00\00\0c\00\00\00\05\07\00\00\00request\00\00\00\00")
  (data (;5;) (i32.const 2080) "\00\00\00\00)\00\00\00\05$\00\00\00org.accordproject.helloworld.Request\00\00\00\00\00\00\00")
  (data (;6;) (i32.const 2136) "\00\00\00\00\0b\00\00\00\05\06\00\00\00$$main\00\00\00\00\00")
  (data (;7;) (i32.const 2160) "\00\00\00\00\0a\00\00\00\05\05\00\00\00$left\00\00\00\00\00\00")
  (data (;8;) (i32.const 2184) "\00\00\00\00*\00\00\00\05%\00\00\00org.accordproject.helloworld.Response\00\00\00\00\00\00")
  (data (;9;) (i32.const 2240) "\00\00\00\00\0b\00\00\00\05\06\00\00\00Hello \00\00\00\00\00")
  (data (;10;) (i32.const 2264) "\00\00\00\00\09\00\00\00\05\04\00\00\00name\00\00\00\00\00\00\00")
  (data (;11;) (i32.const 2288) "\00\00\00\00\07\00\00\00\05\02\00\00\00 (\00")
  (data (;12;) (i32.const 2304) "\00\00\00\00\0a\00\00\00\05\05\00\00\00input\00\00\00\00\00\00")
  (data (;13;) (i32.const 2328) "\00\00\00\00\06\00\00\00\05\01\00\00\00)\00\00")
  (data (;14;) (i32.const 2344) "\00\00\00\00\0b\00\00\00\05\06\00\00\00output\00\00\00\00\00")
  (data (;15;) (i32.const 2368) "\00\00\00\00\0b\00\00\00\05\06\00\00\00$class\00\00\00\00\00")
  (data (;16;) (i32.const 2392) "\00\00\00\00\0a\00\00\00\05\05\00\00\00$data\00\00\00\00\00\00")
  (data (;17;) (i32.const 2416) "\00\00\00\00\0f\00\00\00\05\0a\00\00\00__response\00")
  (data (;18;) (i32.const 2440) "\00\00\00\00:\00\00\00\055\00\00\00org.accordproject.cicero.contract.AccordContractState\00\00\00\00\00\00")
  (data (;19;) (i32.const 2512) "\00\00\00\00<\00\00\00\057\00\00\00org.accordproject.cicero.contract.AccordContractState#1\00\00\00\00")
  (data (;20;) (i32.const 2584) "\00\00\00\00\0c\00\00\00\05\07\00\00\00stateId\00\00\00\00")
  (data (;21;) (i32.const 2608) "\00\00\00\00\01\00\00\00\00\00\00\00\00\00\00\00"))
