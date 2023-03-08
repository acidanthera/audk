## @file
# Makefile
#
# Copyright (c) 2007 - 2016, Intel Corporation. All rights reserved.<BR>
# SPDX-License-Identifier: BSD-2-Clause-Patent
#

DEPFILES = $(OBJECTS:%.o=%.d)

$(MAKEROOT)/libs-$(HOST_ARCH):
	mkdir -p $(MAKEROOT)/libs-$(HOST_ARCH)

.PHONY: install
install: $(MAKEROOT)/libs-$(HOST_ARCH) $(LIBRARY)
	cp $(LIBRARY) $(MAKEROOT)/libs-$(HOST_ARCH)

$(LIBRARY): $(OBJECTS)
	$(AR) crs $@ $^

$(EDK2_OBJPATH)/%.o : $(EDK2_PATH)/%.c
	@mkdir -p $(@D)
	$(CC)  -c $(CPPFLAGS) $(CFLAGS) $(EDK2_INCLUDE) $< -o $@

%.o : %.c
	$(CC)  -c $(CPPFLAGS) $(CFLAGS) $< -o $@

%.o : %.cpp
	$(CXX) -c $(CPPFLAGS) $(CXXFLAGS) $< -o $@

.PHONY: clean
clean:
	@rm -f $(OBJECTS) $(LIBRARY) $(DEPFILES)
	@rm -rf $(EDK2_OBJPATH)

-include $(DEPFILES)
