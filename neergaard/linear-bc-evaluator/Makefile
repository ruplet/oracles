# (Linear) BC evaluator.  
#  $Id: Makefile,v 1.3 2003/11/23 18:45:50 turtle Exp $
# 
#  Copyright 2003 Peter Møller Neergaard and Harry Mairson.
# 
#  This file is part of BC Evaluator.
# 
#  BC Evaluator is free software; you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation; either version 2 of the License, or
#  (at your option) any later version.
# 
#  BC Evaluator is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
# 
#  You should have received a copy of the GNU General Public License
#  along with BC Evaluator; if not, write to the Free Software
#  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
# 
# 
# This file contains the Makefile to work with Henning Makholm's mosmake 
# which makes dependencies for Moscow ML. 

MOSMLC = mosmlc
PERL = perl
MOSMLFLAGS = 
MOSMAKE = /usr/local/mosmake
include $(MOSMAKE)/Makefile.inc

# A hack that remcomples all the modules 
all: $(patsubst %.sml,%.uo,$(wildcard *.sml))

