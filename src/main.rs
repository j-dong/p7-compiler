/*
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

extern crate p7_compiler;

static SAMPLE_CODE: &str = r###"
    global my_var;
    main(arg1 arg2) {
        print "hello world";
    }
"###;

fn main() {
    println!("{:#?}", p7_compiler::parser::ProgramParser::new().parse(SAMPLE_CODE).unwrap());
}
